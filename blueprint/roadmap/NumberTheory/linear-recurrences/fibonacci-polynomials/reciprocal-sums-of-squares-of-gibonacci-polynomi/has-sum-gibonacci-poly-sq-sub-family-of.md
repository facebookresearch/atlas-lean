# Reciprocal sums of shifted squares of the Fibonacci or Lucas polynomials, with the Catalan constant

**Reciprocal sums of shifted squares of the Fibonacci or Lucas polynomials, with the Catalan
constant.** Let `x > 0`, let `g` be the Fibonacci polynomials `f_n` or the Lucas polynomials
`l_n`, and let `C = g_1(x)^2 - g_0(x) g_2(x)` (`C = 1` for `f` and `C = -(x^2 + 4)` for `l`).
For positive integers `k`, `p`, `r`, `t` with `t ≤ 2p` and `α = (x + √(x^2 + 4))/2`, the series
`∑_{n ≥ 0} (-1)^{tk} C f_r(x) f_{2pk}(x) / (g_{(2pn+p+t)k}(x)^2 - (-1)^{tk} C f_{pk}(x)^2)`
converges to `g_{tk+r}(x)/g_{tk}(x) - α^r` (`HasSum`: the series is summable with this sum).
The proof shows that `g_n(x) > 0` for `n ≥ 1`, factors each denominator as
`g_{(2pn+t)k}(x) g_{(2p(n+1)+t)k}(x)` with the Catalan identity, and telescopes.
`tsum_gibonacciPoly_sq_sub_family` takes the sums of the case `g = f`, `C = 1` and of the case
`g = l`, `C = -(x^2 + 4)` from it.
