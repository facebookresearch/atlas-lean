# Dirichlet Green's function of a one-dimensional diffusion

For real functions $b$ and $a$ and real numbers $p$ and $x$, let

$$G(p, x) = \frac{2\, S(\min(p, x))\, \bigl(S(1) - S(\max(p, x))\bigr)}{S(1)\, a(x)\, \psi(x)},$$

with the [scale function](scale-function.md) $S$, the [scale density](scale-density.md) $\psi$ and the convention that division by $0$ gives $0$. For a [regular diffusion](is-regular-diffusion.md), $0 \le p \le 1$ and $0 < x < 1$, it is the Green's function of $-L_{b,a}$ with Dirichlet conditions at $0$ and $1$ ([Green's representation](diffusion-generator-integral-green-funct.md)); when moreover both boundaries are accessible, $G(p, x)\,dx$ is the expected time spent in $(x, x + dx)$ before absorption, starting from $p$. For degenerate coefficients the formula need not invert $-L_{b,a}$: for $a = b = 0$ it gives $G = 0$.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981).
