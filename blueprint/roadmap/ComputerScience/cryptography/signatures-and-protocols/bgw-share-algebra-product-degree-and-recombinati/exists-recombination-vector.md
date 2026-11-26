# Recombination vector for degree-2t sharings

Let `F` be a field, `Party` a finite type and `x : Party → F` injective. If `2
* t < Fintype.card Party`, there is a vector `r : Party → F` such that every
polynomial `p` of natural degree at most `2 * t` satisfies `p.eval 0 = ∑ i, r
i * p.eval (x i)`. This is the BGW multiplication step; `r` is Lagrange
interpolation at `0`.
