# Speed of coming down from infinity of the Beta-coalescent

Let $1 < \alpha < 2$ and let $\Lambda$ be the $\mathrm{Beta}(2 - \alpha, \alpha)$ distribution on
$[0, 1]$. Its [speed of coming down from infinity](speed.md) satisfies

$$v(t) \sim (\alpha\, \Gamma(\alpha))^{1/(\alpha - 1)}\, t^{-1/(\alpha - 1)} \qquad (t \downarrow 0).$$

Indeed, [$\psi(q) \sim c_1 q^\alpha$ as $q \to \infty$ with $c_1 = 1/(\Gamma(\alpha)\, \alpha (\alpha - 1))$](tendsto-psi-div-rpow-beta-lambda.md),
Since $c_1>0$ and $\alpha>1$, comparison with $q^{-\alpha}$ makes $1/\psi$ integrable on a tail, so Grey's condition holds. Hence $u(s) = \int_s^\infty dq / \psi(q) \sim s^{1 - \alpha} / (c_1 (\alpha - 1)) = \alpha\, \Gamma(\alpha)\, s^{1 - \alpha}$
as $s \to \infty$. Since [$u(v(t)) = t$](psi-tail-speed.md) and
[$v(t) \to \infty$ as $t \downarrow 0$](tendsto-speed-zero.md), $t \sim \alpha\, \Gamma(\alpha)\, v(t)^{1 - \alpha}$,
which inverts to the display. For $\alpha = 3/2$ the constant is $9\pi/16$. The constant
$(\alpha\Gamma(\alpha))^{1/(\alpha - 1)}$ tends to $2$, the Kingman constant in $v(t) = 2/t$, as
$\alpha \uparrow 2$; this is a statement about the constants only. The source prints the constant with
exponent $-1/(\alpha - 1)$; the computation above, from the source's own $c_1$ and definition of $v$,
gives $+1/(\alpha - 1)$.

## Depends on

- [The speed of coming down from infinity](speed.md)

## Proof depends on

- [Laplace exponent of the Beta-coalescent](tendsto-psi-div-rpow-beta-lambda.md)
- [The speed inverts the tail integral](psi-tail-speed.md)
- [The speed tends to infinity at zero](tendsto-speed-zero.md)

## Sources

- J. Berestycki, N. Berestycki and V. Limic, "The Λ-coalescent speed of coming down from infinity", Annals of Probability 38 (2010), 207–233, <https://doi.org/10.1214/09-AOP475>, preprint <https://arxiv.org/abs/0807.4278>, Section 3, the discussion of the Beta case after Theorem 1, equation (10).
