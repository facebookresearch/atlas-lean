# Shaft sizing threshold diameter

For a shear factor $c$, bending moment $M$, torque $T$ and allowable $A$, the sizing threshold diameter is

$$d_{\min} = \left(\frac{16 \sqrt{4 M^2 + c\, T^2}}{\pi A}\right)^{1/3},$$

with $\sqrt{x} = 0$ for $x < 0$ and $x / 0 = 0$. Here $x^y$ is the real power: $e^{y \log x}$ for $x > 0$, $\lvert x\rvert^y \cos(\pi y)$ for $x < 0$, and for $x = 0$ it is $1$ when $y = 0$ and $0$ otherwise; in particular $x^{1/3}$ is not the usual real cube root for negative $x$.

For a positive diameter $d$ and a positive allowable $A$ in the calibrated bending–torsion model, the demand is at most $A$ exactly when $d \ge d_{\min}$, and the shaft does not fail (demand strictly below $A$) exactly when $d > d_{\min}$. The threshold is an attained least admissible diameter for the weak inequality only when it is positive: for $M = T = 0$ with a positive shear factor and allowable it is $0$, every positive diameter meets the allowable, and there is no least one.
