# Wright–Fisher diffusion limit, generator form

For every twice continuously differentiable $f : \mathbb{R} \to \mathbb{R}$ and every $x \in [0, 1]$, if $X_M$ has the binomial distribution $\mathrm{Bin}(M, x)$, then

$$M\bigl(\mathbb{E}[f(X_M/M)] - f(x)\bigr) \to \frac{x(1 - x)}{2}\, f''(x) \quad \text{as } M \to \infty:$$

the one-generation generator of the neutral Wright–Fisher chain with $M$ gene copies, sped up by the factor $M$ (time in units of $M$ generations), converges to the neutral Wright–Fisher diffusion generator $L_0$ ([backward generator](../wright-fisher-diffusion/generator.md)).

## Sources

- W. Feller, *Diffusion processes in genetics*, Proc. Second Berkeley Symp. Math. Statist. Probab. (1951), 227–246.
- E. V. Voronovskaya, *Détermination de la forme asymptotique d'approximation des fonctions par les polynômes de M. Bernstein*, C. R. Acad. Sci. URSS (1932), 79–85.
