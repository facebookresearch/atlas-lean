# Stage Zero Row Criterion

Let `C` have a zero object and a Waldhausen structure without gluing,
and let `A : Ar n ⥤ C`. Assume independently that `A.obj (diag i)` is
zero for every `i : Fin (n + 1)`. Also assume, for every `i ≤ j`, including
`i = j`, that the maps `A(0,i) ⟶ A(0,j) ⟶ A(i,j)` form a cofiber sequence:
its legs are `A.map (horiz (Fin.zero_le i) hij)` and
`A.map (vert (Fin.zero_le i) hij)`. Then `IsStage n A` holds, giving a
cofiber sequence `A(i,j) ⟶ A(i,k) ⟶ A(j,k)` for every `i ≤ j ≤ k`.
The diagonal-zero assumption is separate from the zero-row cofiber data.
