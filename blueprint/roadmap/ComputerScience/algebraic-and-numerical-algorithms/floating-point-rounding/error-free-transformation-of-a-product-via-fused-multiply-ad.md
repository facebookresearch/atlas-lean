# Error-free transformation of a product via fused multiply-add

In a binary floating-point format with precision $p$, minimum normal exponent $e_{\min}$ (last-place exponents at least
$q_{\min} = e_{\min} - p + 1$), subnormals and round-to-nearest, let $a$ and $b$ be nonzero numbers of the format,
$\pi = \mathrm{fl}(ab)$ and $e = \mathrm{fma}(a, b, -\pi)$, the fused multiply-add rounding $ab - \pi$ once. Let
$e_a = \lfloor \log_2 \lvert a \rvert \rfloor$ and $e_b = \lfloor \log_2 \lvert b \rvert \rfloor$. If $\pi$ is finite and
$e_a + e_b \ge e_{\min} + p - 1$, then the exact residual $ab - \pi$ is a number of the format and $\pi + e = ab$ exactly. That the
product does not underflow is not enough. Without a fused multiply-add, Dekker's TwoProduct with Veltkamp splitting
gives the same identity when none of its operations underflows or overflows, as a separate page.

## Proof

Both $ab$ and $\pi$ are integer multiples of $2^{e_a + e_b - 2p + 2} \ge 2^{q_{\min}}$ and
$\lvert ab - \pi \rvert \le 2^{e_a + e_b + 1 - p}$, so $ab - \pi$ is a number of the format, which the fused multiply-add returns
unrounded.

## Depends on

- [Floating-point numbers of a bounded format](is-float-in.md)
- [Round to nearest, ties to even](fl.md)

## Related topics

- [The relative error bound](abs-fl-sub-le.md)

## Sources

- Accurate Sum and Dot Product — T. Ogita, S. M. Rump, S. Oishi, SIAM J. Sci. Comput. 26(6):1955-1988, 2005, DOI 10.1137/030601818, Sec. 2, eq. (2.3); Algorithm 3.5 (TwoProductFMA); Algorithm 3.3 and Theorem 3.4, eq. (3.3) (TwoProduct). <https://ogilab.w.waseda.jp/ogita/math/doc/2005_OgRuOi.pdf>
