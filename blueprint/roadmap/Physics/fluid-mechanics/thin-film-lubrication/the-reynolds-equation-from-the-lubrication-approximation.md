# The Reynolds equation from the lubrication approximation

Let $h$ be a smooth positive function on $[0, L]$, let $\mu > 0$ and real $U$ be given, and let $P$ be twice continuously differentiable on
$[0, L]$. In the lubrication approximation of a thin gap $0 < Y < h(x)$ whose lower wall moves with speed $U$ and whose upper wall is at rest,
the velocity $u(x, Y)$ in each cross-section solves

$$\mu\,\frac{\partial^2 u}{\partial Y^2} = \frac{dP}{dx} \quad (0 < Y < h(x)), \qquad u(x, 0) = U, \quad u(x, h(x)) = 0 .$$

For each $x$ this two-point problem has exactly one solution, the Couette-Poiseuille profile

$$u(x, Y) = \frac{1}{2\mu}\,\frac{dP}{dx}\,\big(Y^2 - Y h(x)\big) + U\Big(1 - \frac{Y}{h(x)}\Big),$$

with flux $q(x) = \int_0^{h(x)} u\,dY = -\frac{h^3}{12\mu}\frac{dP}{dx} + \frac{Uh}{2}$. The flux is constant on $[0, L]$ if and only if $P$ solves the
Reynolds equation

$$\frac{d}{dx}\left(h^3\,\frac{dP}{dx}\right) = 6\mu U\,\frac{dh}{dx},$$

and for given end pressures $P(0) = P_0$ and $P(L) = P_L$ the Reynolds equation has exactly one solution, namely
$P' = 6\mu U/h^2 - 12\mu q/h^3$ with the constant $q$ fixed by $P_L - P_0 = \int_0^L \big(6\mu U h^{-2} - 12\mu q h^{-3}\big)\,dx$.

## Sources

- R. L. Panton, *Incompressible Flow*, 4th edition, Wiley, 2013, for the lubrication approximation.
