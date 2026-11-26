# Tensor product to the free sheaf on a product set

Let `(C,J,R)` be a commutative ringed site at universe `u` with weak additive sheafification,
monoidal `J.W`, and the locally-bijective and underlying-ring comparisons. For `A,B : Type u`,
`forwardHom R A B : free_{R_s} A ⊗ free_{R_s} B → free_{R_s}(A × B)` descends from the
second-index cofan, with component at `b` equal to `innerDesc R A B b`. It sends the
tensor-basis inclusion at `(a,b)` to `ιFree (a,b)`. Here `R_s` is the underlying ring sheaf of
`R`.
