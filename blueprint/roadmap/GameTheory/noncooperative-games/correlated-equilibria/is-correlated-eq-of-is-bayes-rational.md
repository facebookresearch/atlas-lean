# Correlated equilibrium as an expression of Bayesian rationality

Let $p$ be a common prior on a finite set $\Omega$ of states, $\mathcal P_i$ the information
partitions of the players of a finite game, and $s(\omega)$ the profile of actions at $\omega$,
each player knowing its own action ($s_i$ is constant on the cells of $\mathcal P_i$). If every
player is Bayes rational at every state, then the distribution of $s$,

$$\psi(t) = p\{\omega : s(\omega) = t\},$$

is a correlated equilibrium.

The proof is Aumann's: for player $i$, recommendation $j$ and deviation $k$, the event
$\{s_i = j\}$ is a union of cells of $\mathcal P_i$; Bayes rationality on each such cell, multiplied
by its probability and summed over the cells, is the correlated-equilibrium inequality.

Statement and source agree, with costs in place of payoffs. The correlated equilibrium is in the
sense of [Correlated equilibrium](is-correlated-eq.md) (the distributional definition of Hart and
Mas-Colell, which is how Aumann's Main Theorem phrases its conclusion: "the distribution of the
action $n$-tuple $s$ is a correlated equilibrium distribution").

## Informally uses

- [Bayes rationality without normalisation](is-bayes-rational-iff-sum.md): the cell-wise
  inequality.
- [Summing over the cells (inequality)](../common-knowledge-and-the-agreement-theorem/sum-nonpos-of-forall-sum-cell-nonpos.md):
  the summation over the cells of $\mathcal P_i$.

## Background

- [Agreement theorem](../common-knowledge-and-the-agreement-theorem/agreement.md): the same
  partition model with a common prior.
- [Nash equilibria are correlated equilibria](is-correlated-eq-product-dist.md): the case of
  independent randomisation.

## Sources

- R. J. Aumann, "Correlated equilibrium as an expression of Bayesian rationality", Econometrica 55(1) (1987), 1–18, §3, Main Theorem and its proof (p. 7–8), and condition (2.2) of §2.
