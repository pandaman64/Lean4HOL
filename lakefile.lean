import Lake
open Lake DSL

package «lean4HOL» {
  -- add package configuration options here
}

lean_lib «Lean4HOL» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lean4HOL» {
  root := `Main
}
