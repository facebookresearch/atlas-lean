# Green's representation for a regular diffusion

Let $b$ and $a$ define a [regular diffusion](is-regular-diffusion.md): $a$ positive and continuous on $(0, 1)$, and $b/a$ continuous on $(0, 1)$ and integrable on $[0, 1]$. Let $g$ be continuous on $(0, 1)$ and such that, for every $q \in (0, 1)$, the function $S g/(a\psi)$ is integrable on $[0, q]$ and $(S(1) - S)\, g/(a\psi)$ is integrable on $[q, 1]$, with the [scale function](scale-function.md) $S$ and the [scale density](scale-density.md) $\psi$. Then for every $p \in (0, 1)$ the function

$$v(q) = \int_0^1 G(q, x)\, g(x)\, dx,$$

with the [Green's function](green-function.md) $G$, satisfies $(L_{b,a} v)(p) = -g(p)$. The integrability conditions hold for every $g$ continuous on $[0, 1]$ under genic selection, where $S/(a\psi)$ is bounded near $0$ and $(S(1) - S)/(a\psi)$ near $1$.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981).
