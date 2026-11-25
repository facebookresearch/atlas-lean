# Quadrant probability for two directions

For unit vectors $u$, $v$ of a finite-dimensional real inner product space and a standard
Gaussian vector $r$,

$$\Pr[\langle u, r\rangle > 0,\ \langle v, r\rangle > 0] = \frac14 + \frac{\arcsin \langle u, v\rangle}{2\pi}.$$

The four sign patterns of $(\langle u, r\rangle, \langle v, r\rangle)$ have total probability $1$; the two mixed
patterns together have probability $\arccos\langle u, v\rangle / \pi$; the symmetry $r \mapsto -r$ of the
standard Gaussian exchanges the two pure patterns; and the boundary hyperplanes are null. So each
pure pattern has probability $\frac12\left(1 - \frac{\arccos \langle u, v\rangle}{\pi}\right)$, which is the formula since
$\arccos = \frac{\pi}{2} - \arcsin$.

## Informally uses

- [Separation probability of two directions](std-gaussian-sign-ne.md): the mixed patterns.
- [Hyperplanes through the origin are null](std-gaussian-inner-eq-zero.md): strict and weak
  inequalities give the same probability.
