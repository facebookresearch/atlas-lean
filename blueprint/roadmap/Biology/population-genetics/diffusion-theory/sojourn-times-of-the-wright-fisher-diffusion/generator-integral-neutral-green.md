# Green's representation for the neutral Wright–Fisher diffusion

For every continuous function $g$ on $\mathbb{R}$ and every $p \in (0, 1)$, the function

$$u(q) = \int_0^1 G(q, x)\, g(x)\, dx,$$

with the [neutral Green's function](neutral-green.md) $G$, satisfies $(L_0 u)(p) = -g(p)$, where $L_0$ is the neutral [backward generator](../wright-fisher-diffusion/generator.md). In the diffusion reading, $u(p)$ is the expected value of $\int_0^T g(X_t)\, dt$ up to the absorption time $T$.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
