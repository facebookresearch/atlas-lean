# Right Action Pow

Recursive iterated right-module action:
`R.functor.obj ((monadPow T (n+1)).obj X) ⟶ R.functor.obj ((monadPow T n).obj X)`.
Degree zero is definitionally `R.action.app X`; successor is definitionally the preceding
iterated action evaluated at `T.obj X`. This avoids `eqToHom` transports for the right
endpoint while keeping left-associated `monadPow` and all pure `mu`/`eta` coherence.
