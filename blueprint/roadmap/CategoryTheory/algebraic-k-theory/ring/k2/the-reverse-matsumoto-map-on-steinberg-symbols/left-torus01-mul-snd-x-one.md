# Left Torus01 mul snd X one

Target theorem `leftTorus01_mul_snd_X_one`: the product of the finite torus words
`h_{01}(u) = w_{01}(u) w_{01}(-1)` acts on `X_one` via `snd` as the product of the
Tits lifts `hTits`.  The proof reuses the `leftTorus01_snd_X_one` bridge for the
first factor `v`, then computes the action of `w_{01}(-1)` and `w_{01}(u)` on that
intermediate point using the Bruhat `fst`/`snd` APIs.
