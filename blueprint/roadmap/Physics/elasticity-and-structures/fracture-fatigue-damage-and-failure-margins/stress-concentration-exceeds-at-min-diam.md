# With $M \ne 0$, a stress concentration $K > 1$ overloads $d_{\min}$

Let $\Phi$ be [calibrated on the bending–torsion states](bending-torsion-calibrated.md) with shear
factor $c$, let $M \ne 0$, $A > 0$ and $K > 1$, and let $T$ be any real number. Let
$d_{\min} = (16 \sqrt{4 M^2 + c T^2}/(\pi A))^{1/3}$ be the [minimum
diameter](shaft-min-diameter.md), and $\sigma$ and $\tau$ the [bending](shaft-bending-stress.md) and
[shear](shaft-shear-stress.md) stresses of a solid circular shaft of diameter $d_{\min}$ under $M$
and $T$. Then the nominal demand equals the allowable, and the demand with the bending stress
multiplied by the stress-concentration factor $K$ exceeds it:

$$\Phi(S(\sigma, \tau)) = A , \qquad A < \Phi(S(K \sigma, \tau)) .$$

So the nominal sizing covers a plain shaft only; a notch or shoulder needs its stress-concentration
factor as an input. The bending moment must be nonzero: for $M = 0$, $\sigma = 0$ and the factor has
no effect.
