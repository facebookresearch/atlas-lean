# Measure

Let $X$ be a set and let $\mathcal{M}$ be a σ-algebra on $X$. A measure on $(X, \mathcal{M})$ is a
function $\mu \colon \mathcal{M} \to [0, \infty]$ such that $\mu(\emptyset) = 0$ and

$$\mu\Big(\bigcup_{k=1}^\infty E_k\Big) = \sum_{k=1}^\infty \mu(E_k)$$

for every sequence $E_1, E_2, \ldots$ of pairwise disjoint sets in $\mathcal{M}$, the sum being taken in
$[0, \infty]$. A measure space is a triple $(X, \mathcal{M}, \mu)$ in which $\mu$ is a measure on
$(X, \mathcal{M})$.

## Depends on

- [σ-algebra](../../../measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/measurable-space.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definition 2.54 (version read: the open-access PDF dated 12 June 2026).
