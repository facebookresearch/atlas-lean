# The time-changed coalescent as the limit of a Wright–Fisher model of varying size

Let $\eta$ be measurable and piecewise continuous with $a \le \eta \le b$ for constants $0 < a \le b$, and consider the neutral Wright–Fisher model whose population size in generation $g$ is $M_g = \lfloor M \eta(g/M) \rfloor$. Then for every $t \ge 0$, the number of ancestral lineages of a sample at generation $\lfloor t M \rfloor$ back converges in law, as $M \to \infty$, to the time-inhomogeneous pure death process that jumps from $k$ to $k - 1$ at rate $\binom{k}{2}/\eta(t)$, that is, Kingman's coalescent run on the clock $R(t) = \int_0^t \eta(s)^{-1}\, ds$.

## Depends on

- [Kingman's theorem for the lineage count](../ancestral-lineage-counting-and-tavar-s-formula/tendsto-wf-lineage-matrix-pow-floor.md)
- [Time-ordered product limit for near-identity matrices](time-ordered-product-limit-for-near-identity-mat.md)

## Expansion

1. The one-generation lineage-count matrices of the model, of the form $I + M^{-1} Y_M(g/M)$ with $Y_M \to Y$, where $Y(s)$ is the block-counting generator divided by $\eta(s)$.
2. The limit by [the time-ordered product limit](time-ordered-product-limit-for-near-identity-mat.md).
3. Checks: constant $\eta$ recovers [Kingman's theorem for the lineage count](../ancestral-lineage-counting-and-tavar-s-formula/tendsto-wf-lineage-matrix-pow-floor.md), and piecewise-constant $\eta$ gives a product of matrix exponentials.

## Sources

- R. C. Griffiths and S. Tavaré, Sampling theory for neutral alleles in a varying environment, *Philos. Trans. R. Soc. Lond. B* 344 (1994), 403–410, <https://pubmed.ncbi.nlm.nih.gov/7800710/> (variable size).
