# Expected divergence

Let $\mu$ be a probability measure on a measurable space $(\Omega, \mathcal{F})$, $\mathcal{G} \subseteq \mathcal{F}$ a sub-σ-algebra, and $\theta, T, f$ real with $f > -1$. Let $\tau$ have the exponential law with rate $2/(1 + f)$ under $\mu$, and let $D$ be a real function whose conditional expectation given $\mathcal{G}$ equals $\theta(T + \tau)$ $\mu$-almost everywhere. Then

$$\int D \, d\mu = \theta\Bigl(T + \frac{1 + f}{2}\Bigr) = m_D(\theta, T, f),$$

the [expected divergence](hka-div-mean.md) (Hudson, Kreitman & Aguadé 1987). No integrability of $D$ is assumed: by the convention that the conditional expectation of a non-integrable function is $0$, the hypothesis then forces $\theta = 0$.

## Sources

- R. R. Hudson, M. Kreitman and M. Aguadé, *A test of neutral molecular evolution based on nucleotide data*, Genetics 116 (1987), 153–159.
