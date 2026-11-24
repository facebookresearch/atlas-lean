# The planar wedge probability

Let $(X, Y)$ be two independent standard normal variables and $0 < a < \pi/2$. The lines through
the origin with normals $(\cos a, -\sin a)$ and $(\cos a, \sin a)$ meet at angle $2a$, and they put
$(X, Y)$ on different sides with probability

$$\Pr\left[\operatorname{sgn}(X \cos a - Y \sin a) \ne \operatorname{sgn}(X \cos a + Y \sin a)\right] = \frac{2a}{\pi},$$

with $\operatorname{sgn} x = 1$ for $x \ge 0$. The proof is in polar coordinates: the density
$e^{-(x^2+y^2)/2}/(2\pi)$ is radial, the event depends only on the angle $\varphi$ (it is
$\cos(\varphi + a)$ against $\cos(\varphi - a)$), the radial integral
$\int_0^\infty r e^{-r^2/2}\, dr$ is $1$, and the angular set is two arcs of length $2a$.

The same computation, through the quadrant probability for two directions, gives Sheppard's
formula.
