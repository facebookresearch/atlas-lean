# Selection duality

For every real $\sigma$, every natural number $n$ and every real $x$, the [Wright–Fisher generator with genic selection](../wright-fisher-diffusion/generator.md) maps $y \mapsto (1 - y)^n$ to

$$\binom{n}{2}\bigl((1 - x)^{n-1} - (1 - x)^n\bigr) + n\sigma\bigl((1 - x)^{n+1} - (1 - x)^n\bigr),$$

where $n - 1$ is read as $0$ when $n = 0$. The dual is the line-counting process of the ancestral selection graph, which is a Markov chain for $\sigma \ge 0$.

## Sources

- S. Mano, *Duality, ancestral and diffusion processes in models with selection*, Theoret. Population Biol. 75 (2009), 164–175.
- S. M. Krone and C. Neuhauser, *Ancestral processes with selection*, Theoret. Population Biol. 51 (1997), 210–237.
