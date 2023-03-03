inductive preterm (α : Type) where
| var : (v : α) → preterm α
| lam : (f : α → preterm α) → preterm α
| app : (m₁ : preterm α) → (m₂ : preterm α) → preterm α

#check @preterm.rec

def Preterm : Type 1 := ∀(α : Type), preterm α

def preterm.repr' : preterm Nat → Nat → String
| .var n, _ => n.repr
| .lam f, lv => s!"(λ{lv.repr}.{preterm.repr' (f lv) (lv + 1)})"
| .app m₁ m₂, lv => s!"({preterm.repr' m₁ lv} {preterm.repr' m₂ lv})"

def preterm.repr (m : Preterm) : String :=
  preterm.repr' (m Nat) 0

instance : Repr Preterm where
  reprPrec (m : Preterm) _ := preterm.repr m

def i : Preterm := λα => .lam (λ(x : α) => .var x)
#eval i
--> (λ0.0)

def s : Preterm := λ_ => .lam (λx => .lam (λy => .lam (λz => .app (.app (.var x) (.var z)) (.app (.var y) (.var z)))))
#eval s

def k : Preterm := λ_ => .lam (λx => .lam (λ_y => .var x))
#eval k

def twikipedia : Preterm :=
  λ_ => .lam (λz => .app
    (.lam (λy => .app (.var y) (.lam (λx => .var x))))
    (.lam (λx => .app (.var z) (.var x))))
#eval (preterm.repr' (twikipedia Nat) 1)
--> "(λ1.((λ2.(2 (λ3.3))) (λ2.(1 2))))", Wikipediaと違う

def n₀ : Preterm := λ_ => .lam (λ_f => .lam (λx => .var x))
def n₁ : Preterm := λ_ => .lam (λf => .lam (λx => .app (.var f) (.var x)))
def n₂ : Preterm := λ_ => .lam (λf => .lam (λx => .app (.var f) (.app (.var f) (.var x))))
def n₃ : Preterm := λ_ => .lam (λf => .lam (λx => .app (.var f) (.app (.var f) (.app (.var f) (.var x)))))

#eval n₀
#eval n₁
#eval n₂
#eval n₃

def succ : Preterm := λ_ => .lam (λn => .lam (λf => .lam (λx => .app (.var f) (.app (.app (.var n) (.var f)) (.var x)))))

def App (m₁ : Preterm) (m₂ : Preterm) : Preterm :=
  λα => .app (m₁ α) (m₂ α)

def succ_n₀ : Preterm := App succ n₀
#eval succ_n₀ -- 簡約されてない
--> ((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1)))

def subst' {α : Type} : preterm (preterm α) → preterm α
| .var x => x
| .lam f => .lam (λx => subst' (f (.var x)))
| .app m₁ m₂ => .app (subst' m₁) (subst' m₂)

def pbeta' {α : Type} : preterm (preterm α) → preterm α
| .var x => x
| .lam f => .lam (λx => pbeta' (f (.var x)))
| .app (.lam f) m => subst' (f (subst' m))
| .app m₁ m₂ => .app (pbeta' m₁) (pbeta' m₂)

def pbeta : Preterm → Preterm :=
  λm _ => pbeta' (m _)

#eval succ_n₀
--> ((λ0.(λ1.(λ2.(1 ((0 1) 2))))) (λ0.(λ1.1)))
#eval pbeta succ_n₀
--> (λ0.(λ1.(0 (((λ2.(λ3.3)) 0) 1))))
#eval pbeta (pbeta succ_n₀)
--> (λ0.(λ1.(0 ((λ2.2) 1))))
#eval pbeta (pbeta (pbeta succ_n₀))
--> (λ0.(λ1.(0 1)))
#eval pbeta (pbeta (pbeta (pbeta succ_n₀)))
--> (λ0.(λ1.(0 1)))

def ω : Preterm := λ_ => .lam (λx => .app (.var x) (.var x))
def Ω : Preterm := App ω ω

#eval Ω
#eval pbeta Ω

-- すげ～～～
