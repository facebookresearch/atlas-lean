# Green's representation with selection

For every real $\sigma$, every continuous function $g$ on $\mathbb{R}$ and every $p \in (0, 1)$, the function

$$v(q) = \int_0^1 \Psi_\sigma(q, x)\, g(x)\, dx,$$

with the [sojourn density](selection-green.md) $\Psi_\sigma$, satisfies $(L_\sigma v)(p) = -g(p)$, where $L_\sigma$ is the [backward generator](../wright-fisher-diffusion/generator.md). With the boundary values $v(0) = 0$ and $v(1) = 0$ ([at frequency zero](integral-selection-green-left.md), [at frequency one](integral-selection-green-right.md)), this extends the [neutral Green representation](../sojourn-times-of-the-wright-fisher-diffusion/generator-integral-neutral-green.md) to $\sigma \ne 0$; in the diffusion reading, $v(p)$ is the expected value of $\int_0^T g(X_t)\, dt$ up to the absorption time $T$.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
