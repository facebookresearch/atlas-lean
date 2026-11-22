# Box free eigen equation

Free differential-expression identity: the sine extension `boxFunction n L` of the `n`-th
box state to all of `ℝ` satisfies `-(ħ^2/2m) ψ'' = E_n ψ` at every real `x` (uses `deriv`
twice; Mathlib `HasDerivAt.deriv`). Outside `[0, L]` this is a property of the extension, not
of the box Hamiltonian, whose states vanish there; `box_eigen_equation` is the eigen-equation
on the interior.
