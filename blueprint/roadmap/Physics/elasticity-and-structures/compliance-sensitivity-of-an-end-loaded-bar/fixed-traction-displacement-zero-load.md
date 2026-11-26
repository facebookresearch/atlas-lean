# With no distributed load the constructed bar displacement is F x / EA

For a bar of rigidity $k$ and length $L$ under an end force $P$ and a distributed load $f$, the
constructed fixed-traction displacement is the primitive, from the fixed end $x = 0$, of the strain
$(P + \int_y^L f(z)\, dz) / k$:

$$u(x) = \int_0^x \frac{P + \int_y^L f(z)\, dz}{k}\, dy.$$

With zero distributed load, rigidity $EA$ and end force $F$ it is, for all real $EA$, $L$, $F$ and
$x$,

$$u(x) = \frac{F x}{EA}.$$

At $EA = 0$ both sides are $0$ by the convention $x / 0 = 0$, and the length $L$ does not enter. In
the physical reading $EA > 0$, $L > 0$ and $0 \le x \le L$; the identity holds for all real inputs,
the integral being oriented for $x < 0$.
