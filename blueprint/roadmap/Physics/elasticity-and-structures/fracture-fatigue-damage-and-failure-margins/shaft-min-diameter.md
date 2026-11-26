# Minimum diameter of a solid circular shaft for an allowable stress

For real numbers $c$ (shear factor), $M$ (bending moment), $T$ (torque) and $A$ (allowable), the
minimum diameter is the real power

$$d_{\min} = \left(\frac{16 \sqrt{4 M^2 + c T^2}}{\pi A}\right)^{1/3} .$$

It is intended for $c > 0$, $A > 0$ and a nonzero load ($M \ne 0$ or $T \ne 0$), where it is
[positive](shaft-min-diameter-pos.md); for a functional
[calibrated on the bending–torsion states](bending-torsion-calibrated.md) with shear factor $c$, a
diameter $d > 0$ and $A > 0$, the demand at the critical point stays within $A$
[exactly when $d \ge d_{\min}$](shaft-demand-le-iff.md). With the conventions $x / 0 = 0$ and
$\sqrt{x} = 0$ for $x < 0$, the base of the power is $0$ when $A = 0$ or $4 M^2 + c T^2 \le 0$ (for
example at zero load), and then $d_{\min} = 0^{1/3} = 0$; when $A < 0$ and $4 M^2 + c T^2 > 0$ the
base $b$ is negative and the real power of a negative base gives
$d_{\min} = |b|^{1/3} \cos(\pi/3) = |b|^{1/3}/2$.
