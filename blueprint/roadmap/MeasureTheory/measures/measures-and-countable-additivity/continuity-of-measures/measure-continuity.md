# Continuity of measures from below and from above

Let $(X, \mathcal{M}, \mu)$ be a measure space and let $E_1, E_2, \ldots$ be sets in
$\mathcal{M}$.

- Continuity from below: if $E_1 \subseteq E_2 \subseteq \cdots$, then
  $\mu\big(\bigcup_{k=1}^\infty E_k\big) = \lim_{k \to \infty} \mu(E_k)$.
- Continuity from above: if $E_1 \supseteq E_2 \supseteq \cdots$ and $\mu(E_1) < \infty$, then
  $\mu\big(\bigcap_{k=1}^\infty E_k\big) = \lim_{k \to \infty} \mu(E_k)$.

Both limits exist in $[0, \infty]$, since the sequences $\mu(E_k)$ are monotone.

## Proof

For continuity from below, put $E_0 = \emptyset$. The sets $E_j \setminus E_{j-1}$, $j \ge 1$, are measurable and
pairwise disjoint, their union is $\bigcup_k E_k$, and the first $k$ of them have union $E_k$. Countable additivity
and finite additivity give

$$\mu\Big(\bigcup_k E_k\Big) = \sum_{j=1}^\infty \mu(E_j \setminus E_{j-1})
= \lim_{k \to \infty} \sum_{j=1}^k \mu(E_j \setminus E_{j-1}) = \lim_{k \to \infty} \mu(E_k).$$

For continuity from above, the sets $E_1 \setminus E_k$ increase to $E_1 \setminus \bigcap_k E_k$, so by the first part
$\mu\big(E_1 \setminus \bigcap_k E_k\big) = \lim_k \mu(E_1 \setminus E_k)$. Since $\mu(E_1) < \infty$, finite
additivity and monotonicity give $\mu(E_1 \setminus F) = \mu(E_1) - \mu(F)$ for every measurable $F \subseteq E_1$,
and subtracting both sides from $\mu(E_1)$ gives the claim.

## Depends on

- [Measure](../measures/measure.md)

## Proof depends on

- [σ-algebra](../../../measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/measurable-space.md)
- [Finite additivity of a measure](../measures/measure-bi-union-finset.md)
- [Monotonicity of a measure](../measures/measure-mono.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, results 2.59 and 2.60 (version read: the open-access PDF dated 12 June 2026).
