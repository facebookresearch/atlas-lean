# A shaft with $d > 0$ does not fail exactly when $d > d_{\min}$

Let $\Phi$ be [calibrated on the bending–torsion states](bending-torsion-calibrated.md) with shear
factor $c$ (so $c > 0$), let $d > 0$ and $A > 0$, and let $M$ and $T$ be real numbers. For the solid
circular shaft of diameter $d$ under the bending moment $M$ and the torque $T$, with the [bending
stress](shaft-bending-stress.md) $\sigma$ and the [shear stress](shaft-shear-stress.md) $\tau$, the
equality-inclusive [failure event](demand-failure.md) $A \le \Phi(S(\sigma, \tau))$ does not hold,
that is the [demand](shaft-demand-eq.md) is strictly below $A$, if and only if $d$ exceeds the
[minimum diameter](shaft-min-diameter.md):

$$\Phi(S(\sigma, \tau)) < A \iff \Bigl(\frac{16 \sqrt{4 M^2 + c T^2}}{\pi A}\Bigr)^{1/3} < d .$$
