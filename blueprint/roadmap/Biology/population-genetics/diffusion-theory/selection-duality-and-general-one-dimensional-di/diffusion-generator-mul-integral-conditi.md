# Conditional mean time to fixation, backward equation

Let $b$ and $a$ define a [regular diffusion](is-regular-diffusion.md) with [scale-function ratio](fixation-prob.md) $u$, such that for every $q \in (0, 1)$ the function $S u/(a\psi)$ is integrable on $[0, q]$ and $(S(1) - S)\, u/(a\psi)$ is integrable on $[q, 1]$. Then for every $p \in (0, 1)$ the function

$$w(q) = u(q) \int_0^1 G^*(q, x)\, dx,$$

with the [conditional sojourn density](conditional-green.md) $G^*$, satisfies $(L_{b,a} w)(p) = -u(p)$.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
