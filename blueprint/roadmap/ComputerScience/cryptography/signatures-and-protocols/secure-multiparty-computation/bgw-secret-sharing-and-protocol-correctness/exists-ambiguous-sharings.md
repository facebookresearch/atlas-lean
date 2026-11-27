# Too few evaluation points do not determine the secret

Let `F` be a field and `Party` a finite type, let `x : Party → F` with `x i ≠
0` for every `i`, and suppose `Fintype.card Party ≤ 2 * t`. Then there are
polynomials `p` and `q` of natural degree at most `2 * t` with `p.eval (x i) =
q.eval (x i)` for every `i` but `p.eval 0 ≠ q.eval 0`. For example, the
vanishing polynomial `∏ i, (X - C (x i))` agrees with `0` at every point but
is nonzero at `0`.
