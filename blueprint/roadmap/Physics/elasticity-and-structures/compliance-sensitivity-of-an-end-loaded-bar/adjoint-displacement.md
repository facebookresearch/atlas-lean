# Scalar adjoint F / k of the compliance

For an end force $F$ and a stiffness $k$, the scalar adjoint is

$$p = \frac{F}{k},$$

a length when $F$ is a force and $k$ a force per length. For $k \ne 0$ it
[solves the adjoint equation](stiffness-mul-adjoint-displacement.md)
$k\, p = \partial J / \partial u_{\mathrm{tip}} = F$, the right side being the derivative of the
load work $J = F\, u_{\mathrm{tip}}$ with respect to the tip displacement. It is the same quotient
as the [tip displacement](tip-displacement.md): the compliance is self-adjoint. At $k = 0$ it is $0$
by the convention $x / 0 = 0$, and then $k\, p = 0$, which equals $F$ only for $F = 0$.

In the physical reading $k > 0$.
