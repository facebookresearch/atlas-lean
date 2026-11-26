# Zero–one law for patterns in size-conditioned Galton–Watson trees

Let $X$ be a nonnegative integer-valued offspring distribution with $\mathbb E(X)=1$, $\mathbb E(X^2)<\infty$ and $\mathbb P(X=0)>0$, let $T\sim\mathrm{GW}(X)$, and let $T_n\sim(T\mid \#T=n)$ for every $n$ with $\mathbb P(\#T=n)>0$. A finite tree $\tau$ is **$X$-realizable** if it can be rooted so that all its out-degrees lie in the support of $X$.

**Theorem (0–1 law).** For every finite tree $\tau$:

1. if $\tau$ is not $X$-realizable, then $\mathbb P(T_n\supset\tau)=0$ for all $n$;
2. if $\tau$ is $X$-realizable, then $\mathbb P(T_n\supset\tau)\to 1$ as $n\to\infty$,

where $T_n\supset\tau$ means that $T_n$ contains a copy of $\tau$.

**Corollaries.** (a) If $T_n$ is uniform among $d$-ary trees with $n$ labelled leaves, then $\mathbb P(T_n\supset\tau)\to 1$ for every finite $d$-ary tree $\tau$. (b) If $N_n$ is uniform among level-$k$ phylogenetic networks with $n$ labelled leaves, then $\mathbb P(N_n\supset\tau)\to 1$ for every finite level-$k$ network $\tau$. In particular, since tree-child networks contain no stacks (a reticulation whose only child is a reticulation) while some level-$2$ networks do, the fraction of level-$k$ networks ($k\ge 2$) that are tree-child tends to $0$.

## Proof depends on

- [Second Borel–Cantelli lemma](../../../../Probability/foundations/borel-cantelli-lemmas/second-borel-cantelli-lemma/measure-limsup-eq-one.md)

## Expansion

The proof uses the local limit of $T_n$ (Kesten's tree, Janson): an infinite spine $v_1,v_2,\dots$ in which $v_k$ receives $X_k^*-1$ extra children, $X^*$ size-biased, each extra child carrying an independent copy of $T$. Since $\tau$ is realizable, each of these independent copies contains $\tau$ with a fixed positive probability, so the limit contains $\tau$ almost surely by Borel–Cantelli; local convergence transfers this to $T_n$ near its root, and the event only becomes easier far from the root. Uniform leaf-labelled $d$-ary trees are obtained from the critical offspring law $X\sim d\cdot\mathrm{Bernoulli}(1/d)$ conditioned on size (with a leaf grafted on the root and labels assigned uniformly), and uniform level-$k$ networks from Stufler's blow-up construction, which yields the corollaries.

## Sources

- F. Bienvenu and M. Steel, "0–1 laws for pattern occurrences in phylogenetic trees and networks", Bulletin of Mathematical Biology 86(8) (2024) 94, <https://doi.org/10.1007/s11538-024-01316-x>, PMCID PMC11561131. Propositions 6 and 8, Theorems 10 and 12, Corollaries 13–14 and Remark 15 (Section 3).
