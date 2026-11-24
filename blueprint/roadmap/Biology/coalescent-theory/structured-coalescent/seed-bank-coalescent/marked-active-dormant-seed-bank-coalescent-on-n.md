# The seed-bank coalescent on the natural numbers

Let $c, K \in (0, \infty)$. The [seed-bank $k$-coalescents](seed-bank-coalescent-active-dormant-lineages.md) started from the partition of
$\{1, \dots, k\}$ into singletons, all marked active, are consistent under restriction of marked partitions from $\{1, \dots, k + 1\}$ to $\{1, \dots, k\}$, and
there is a process on marked partitions of $\mathbb N$, unique in law, whose restriction to
$\{1, \dots, k\}$ is the seed-bank $k$-coalescent for every $k$: the seed-bank coalescent with seed-bank
intensity $c$ and relative seed-bank size $1/K$. Its restrictions can be chosen right-continuous with
left limits for the discrete topology on marked partitions. A single lineage passes from active to dormant
and back with positive probability in any time interval, so the marks are not monotone in time, and the
partition obtained by forgetting the marks is not Kingman's coalescent: two lineages started active have
expected time $((1 + K)/K)^2 > 1$ to their common ancestor.

## Depends on

- [Seed-bank coalescent](seed-bank-coalescent-active-dormant-lineages.md)

## Proof depends on

- [Finite-dimensional distributions of the path process](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md)
- [Kolmogorov extension theorem](../../../../Probability/foundations/kolmogorov-extension-theorem/kolmogorov-extension.md)

## Expansion

A sound expansion checks the intertwining of the marked rate matrices with the restriction map:
transitions of blocks that meet $\{1, \dots, k\}$ act on the restriction in the same way and at the same
rates, while mergers and flag changes involving the singleton $\{k + 1\}$ alone are invisible in it. Path consistency then
follows as for [the Λ-coalescent](../../coalescents/path-laws-of-the-coalescent-on-a-finite-sample-a.md), and the Kolmogorov extension theorem over pairs of a sample
size and a rational time gives the process on $\mathbb N$. Since marks switch in both directions, the
paths are not monotone; right limits exist because each restriction has bounded rates and therefore
finitely many jumps on bounded intervals almost surely.

## Sources

- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, "A new coalescent for seed-bank models", Annals of Applied Probability 26 (2016), 857–891, <https://doi.org/10.1214/15-AAP1106>, preprint <https://arxiv.org/abs/1411.4747>, Section 3, Definitions 3.1 and 3.2 and Remark 3.3.
