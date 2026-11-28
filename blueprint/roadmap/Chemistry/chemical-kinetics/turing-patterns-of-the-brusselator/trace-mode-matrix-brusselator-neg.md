# For b < 1 + a², the neutral mode matrix has negative trace

Let $a \ne 0$, $b < 1 + a^2$, $d_u \ge 0$, and let $k$ be real with $(b - 1) k^2 - d_u k^4 > 0$. Let
$d_0 = d_n(k^2)$ be the [neutral inhibitor diffusion](brusselator-neutral-diffusion.md) of $k^2$ and
$J$ the [Brusselator Jacobian](brusselator-jacobian.md). Then

$$\operatorname{tr} J - k^2 (d_u + d_0) < 0,$$

that is, the
[mode matrix](../../../Biology/pattern-formation/turing-patterns-and-diffusion-driven-instability/mode-matrix.md)
$J - k^2 \operatorname{diag}(d_u, d_0)$ has negative trace. Its determinant is $0$ by the choice of
$d_0$, so its eigenvalues are $0$ and this negative trace.
