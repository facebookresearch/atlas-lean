# Blade-element momentum equations for a rotor annulus

This node covers the blade-element momentum equations of a horizontal-axis rotor. Consider an annulus of radius $r > 0$ and width $dr$
of a rotor with $B$ blades, chord $c(r)$ and angular speed $\Omega > 0$ in a uniform wind $U_\infty > 0$, with axial and tangential induction
factors $a < 1$ and $a' > -1$. Equate the axial thrust and torque on the annulus given by one-dimensional axial and angular momentum balances,
$dT = 4\pi\rho U_\infty^2 a(1 - a) r\,dr$ and $dQ = 4\pi\rho U_\infty\Omega a'(1 - a) r^3\,dr$, with those given by the blade sections through
their lift and drag coefficients $C_L$, $C_D$ at the relative flow angle $\varphi \in (0, \pi/2)$ given by $\tan\varphi = U_\infty(1 - a)/(\Omega r(1 + a'))$, so that $\sin\varphi\cos\varphi \ne 0$. With local
solidity $\sigma' = Bc/(2\pi r)$, $C_n = C_L\cos\varphi + C_D\sin\varphi$ and $C_t = C_L\sin\varphi - C_D\cos\varphi$, the induction factors satisfy

$$\frac{a}{1 - a} = \frac{\sigma' C_n}{4\sin^2\varphi}, \qquad \frac{a'}{1 + a'} = \frac{\sigma' C_t}{4\sin\varphi\cos\varphi}.$$

## Expansion

A good expansion first fixes the sign conventions for thrust, torque and the relative velocity triangle, then states the two
momentum balances and the blade-element forces as separate model inputs, and derives the displayed equations from them. Existence of a
solution $(a, a')$ for given coefficient maps, tip-loss corrections and the high-induction regime are separate nodes; the coefficient maps
are data, not consequences.

## Sources

- J. F. Manwell, J. G. McGowan and A. L. Rogers, *Wind Energy Explained: Theory, Design and Application*, 2nd edition, Wiley, 2009, for blade-element momentum theory.
