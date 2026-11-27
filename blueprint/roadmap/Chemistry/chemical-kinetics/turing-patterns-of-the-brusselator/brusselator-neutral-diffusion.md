# Neutral inhibitor diffusion of the Brusselator

For real numbers $a$, $b$, $d_u$ and $q$, let

$$d_n(q) = \frac{a^2 (1 + d_u q)}{(b - 1) q - d_u q^2},$$

with the convention $x / 0 = 0$, so $d_n(q) = 0$ where $(b - 1) q - d_u q^2 = 0$, for example at
$q = 0$. For the [Brusselator Jacobian](brusselator-jacobian.md) $J$ it is the
[neutral diffusion](../../../Analysis/partial-differential-equations/bifurcation-of-turing-pattern-branches/neutral-diffusion.md)
of squared wavenumber $q$ ([closed form](neutral-diffusion-brusselator-jacobian.md)): when the
denominator is nonzero, $d_n(q)$ is the only inhibitor diffusion coefficient $d_v$ with
$\det(J - q \operatorname{diag}(d_u, d_v)) = 0$. The intended domain is $q > 0$ with a positive
denominator (an admissible squared wavenumber).
