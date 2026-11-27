# No recombination vector with too few points

Let `F` be a field and `Party` a finite type, let `x : Party → F` with `x i ≠
0` for every `i`, and suppose `Fintype.card Party ≤ 2 * t`. Then there is no
vector `r : Party → F` such that `p.eval 0 = ∑ i, r i * p.eval (x i)` for
every polynomial `p` of natural degree at most `2 * t`: any candidate gives
the same output on two degree-`2 * t` polynomials that agree at every point
but differ at `0`.
