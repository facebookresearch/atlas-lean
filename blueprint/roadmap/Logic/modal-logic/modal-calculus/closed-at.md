# μ-calculus formula closed at a given binding depth

A formula is closed at depth `d` when every free de Bruijn variable is `< d`:
only `μ` / `ν` increase the depth; `□` / `◇` do not bind variables and preserve it.
