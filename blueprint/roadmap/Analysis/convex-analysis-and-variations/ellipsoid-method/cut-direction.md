# Direction of a central-cut step

For a matrix $A$ and a vector $c$, the cut direction is

$$
b = \frac{A c}{\sqrt{c^\top A c}} .
$$

When $A$ is positive definite and $c \ne 0$, $c^\top A c > 0$ and $b$ is the point of $\partial E(0, A)$ that maximises $c^\top x$ over $E(0, A)$.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, the vector $b$ defined after equation (3).
