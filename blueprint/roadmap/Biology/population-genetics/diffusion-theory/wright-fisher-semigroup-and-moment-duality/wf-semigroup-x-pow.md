# Moment duality for the diffusion

For every real $t \ge 0$, every natural number $n$ and every $x \in [0, 1]$, the [Wright–Fisher diffusion semigroup](wf-semigroup.md) applied to $y \mapsto y^n$ is

$$(T_t\, y^n)(x) = \sum_{k=0}^{n} \bigl(e^{t G_n}\bigr)(n, k)\, x^k,$$

where $e^{t G_n}$ is the transition matrix of [Kingman's block-counting process](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/block-counting-generator.md). In process language, $\mathbb{E}_x[X_t^{\,n}] = \mathbb{E}_n[x^{A_t}]$ for the diffusion $X$ and the block-counting process $A$.

## Sources

- S. N. Ethier and R. C. Griffiths, *The transition function of a Fleming–Viot process*, Ann. Probab. 21 (1993), 1571–1590.
