# Error-free transformation of a product via fused multiply-add

In a binary floating-point format with precision $p \ge 1$ and bounded last-place exponents
$[q_{\min},q_{\max}]$, set $e_{\min}=q_{\min}+p-1$. Let $a$ and $b$ be nonzero format numbers,
let $\pi = \mathrm{fl}(ab)$ be the nearest-even rounded product, and let $e$ be the result of
rounding the exact fused expression $ab-\pi$ once. Write $e_a = \lfloor \log_2 |a| \rfloor$
and $e_b = \lfloor \log_2 |b| \rfloor$. If $\pi$ belongs to the bounded format and
$e_a + e_b \ge e_{\min} + p - 1$, then $ab - \pi$ belongs to the format, possibly as a
subnormal, and $\pi + e = ab$ exactly as values. The theorem uses the unbounded-exponent
nearest-even function for rounding and separately checks bounded-format membership. It does not
assume that the exact product is at most the largest finite value in magnitude, model IEEE status
flags, or round the reconstruction sum. Dekker's TwoProduct without a fused multiply-add is a
separate result.

## Proof

With $g=e_a+e_b-2p+2$, both $ab$ and $\pi$ are integer multiples of $2^g$. The hypothesis gives
$q_{\min}\le g$, and membership of $\pi$ in the bounded format supplies $g\le q_{\max}$. The rounding
error is at most half a last-place unit of $ab$. Since the product's log exponent is either
$e_a+e_b$ or $e_a+e_b+1$, the residual's magnitude is strictly less than $2^{g+p}$. Its integer
coefficient on the grid $2^g$ therefore fits in $p$ bits. Rounding returns that residual unchanged.
For example, at precision $3$ and last-place exponents $[0,3]$, the exact product $7\cdot7=49$
rounds to $48$ and the residual $1$ is subnormal.

## Related topics

- [The relative error bound](abs-fl-sub-le.md)

## Sources

- Accurate Sum and Dot Product — T. Ogita, S. M. Rump, S. Oishi, SIAM J. Sci. Comput. 26(6):1955-1988, 2005, DOI 10.1137/030601818, Sec. 2, eq. (2.3); Algorithm 3.5 (TwoProductFMA); Algorithm 3.3 and Theorem 3.4, eq. (3.3) (TwoProduct). <https://ogilab.w.waseda.jp/ogita/math/doc/2005_OgRuOi.pdf>
