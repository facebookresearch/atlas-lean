# Holding times and jump chain of Kingman's n-coalescent are independent

Let $n \ge 2$ and let $X^n$ be Kingman's $n$-coalescent, the
[continuous-time Markov chain path process](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md) with
[Kingman's partition rate matrix](partition-rate.md) started from the partition of $\{1, \dots, n\}$ into singletons. Let
$\Sigma_n, \Sigma_{n-1}, \dots, \Sigma_1$ be the successive partitions it visits ($\Sigma_k$ has $k$ blocks) and
$T_k$ the time it spends in $\Sigma_k$, $2 \le k \le n$. Then $T_n, \dots, T_2$ are independent,
$T_k \sim \mathrm{Exp}\binom k2$, and $(T_k)_{2 \le k \le n}$ is independent of $(\Sigma_k)_{1 \le k \le n}$, whose
transition from a partition with $k$ blocks chooses each pair of blocks with probability $1/\binom k2$ and merges it. Its marginal at $\Sigma_k$ is the [jump-chain law after $n-k$ jumps](jump-law.md), given by [Kingman's formula](jump-law-eq.md). In particular $(T_k)$ is a
[family of Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md), so the time to the most recent common ancestor of the
sample, $\sum_{k=2}^n T_k$, has [expectation $2(1 - 1/n)$](../kingman-s-coalescent-and-watterson-s-estimator/integral-tmrca.md).

## Depends on

- [Kingman's partition rate matrix](partition-rate.md)
- [Path process of a finite continuous-time Markov chain](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)
- [Law of the jump chain of Kingman's coalescent](jump-law.md)
- [Kingman holding times](../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md)

## Proof depends on

- [Holding times of the path process](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-holding-time.md)
- [Kingman's formula for the jump chain](jump-law-eq.md)
- [Law of the step sequence](../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure.md): independent step maps and exponential clocks in the actual path construction.
- [Expected time to the most recent common ancestor](../kingman-s-coalescent-and-watterson-s-estimator/integral-tmrca.md): the stated finite-sample expectation.

## Expansion

A sound expansion reads the statement off the jump-chain and holding-time construction of the path
process: the holding time in the $j$-th state visited is $E_j / q(Y_j)$, where the clocks $E_j$ are
independent $\mathrm{Exp}(1)$ variables independent of the jump maps, and the exit rate
$q(\pi) = \binom{|\pi|}{2}$ depends only on the number of blocks, which is $n - j$ in the $j$-th state visited
because each jump merges two blocks. Hence $T_{n-j} = E_j / \binom{n-j}{2}$ is a function of the clocks
alone.

## Sources

- J. F. C. Kingman, "The coalescent", Stochastic Processes and their Applications 13 (1982), 235–248, <https://doi.org/10.1016/0304-4149(82)90011-4>, Section 2, Theorem 1 (independence of the death process and the jump chain, and the transition and absolute probabilities (2.2)–(2.3) of the jump chain).
- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", Theoretical Population Biology 26 (1984), 119–164, <https://doi.org/10.1016/0040-5809(84)90027-3>, Section 7.2 (the $i$-coalescent spends an exponential time with mean $2/(l(l - 1))$ in its state with $l$ classes, independently of the jump chain).
