# The tower step of the agreement theorem

Let $\mu$ be a finite measure on a finite set $\Omega$ of states in which every singleton is measurable,
let the partition $\mathcal P$ be finer than $\mathcal Q$, and let $Q$ be a cell of $\mathcal Q$. If the posterior of
$A$ given $\mathcal P$ equals $a$ at every state of $Q$, then

$$\mu(A \cap Q) = a\,\mu(Q).$$

Indeed $Q$ is a disjoint union of cells $P_j$ of $\mathcal P$, on each of which
$\mu(A \cap P_j) = a\,\mu(P_j)$; summing over $j$ gives the claim. No cell needs to be nonnull: on
a null cell $P_j$ both sides vanish.

## Informally uses

- [Summing over the cells (equality)](sum-eq-zero-of-forall-sum-cell-eq-zero.md): the summation
  over the cells of $\mathcal P$.

## Background

- [Posterior probability](posterior.md): the hypothesis.

## Sources

- R. J. Aumann, "Agreeing to disagree", Ann. Statist. 4(6) (1976), 1236–1239, p. 1237 (proof of the Proposition: "$p(A \cap P_j) = q_1 p(P_j)$ for all $j$; hence by summing over $j$ we get $p(A \cap P) = q_1 p(P)$").
