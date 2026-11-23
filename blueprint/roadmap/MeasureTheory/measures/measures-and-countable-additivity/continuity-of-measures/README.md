# Continuity of measures from below and from above

Let $(X, \mathcal{M}, \mu)$ be a measure space and let $E_1, E_2, \ldots \in \mathcal{M}$. If
$E_1 \subseteq E_2 \subseteq \cdots$, then $\mu\big(\bigcup_k E_k\big) = \lim_{k \to \infty} \mu(E_k)$. If
$E_1 \supseteq E_2 \supseteq \cdots$ and $\mu(E_1) < \infty$, then
$\mu\big(\bigcap_k E_k\big) = \lim_{k \to \infty} \mu(E_k)$. The limits are taken in $[0, \infty]$.

## Idea

Continuity from below comes from writing the union as the disjoint union of the differences
$E_k \setminus E_{k-1}$ and using countable additivity; continuity from above follows by applying it to the sets
$E_1 \setminus E_k$, which is where $\mu(E_1) < \infty$ is needed. That hypothesis cannot be dropped: for counting
measure on $\mathbb{N}$, the sets $\{k, k + 1, \ldots\}$ decrease to $\emptyset$ but all have measure $\infty$.
Continuity from below is the key step in the proof of the monotone convergence theorem, and continuity from above
gives, for instance, the right-continuity of distribution functions,
$P(X \le x) = \lim_n P(X \le x + 1/n)$.

## Statements

- [Continuity of measures from below and from above](measure-continuity.md)
- [Continuity from below for increasing families of sets](tendsto-measure-i-union-at-top.md): continuity from below for sets that need not be measurable, in families indexed by a preorder such as $\mathbb{N}$ or $\mathbb{R}$.

## Background

- [Measures](../measures/README.md): measures

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, results 2.59 and 2.60 (version read: the open-access PDF dated 12 June 2026).
