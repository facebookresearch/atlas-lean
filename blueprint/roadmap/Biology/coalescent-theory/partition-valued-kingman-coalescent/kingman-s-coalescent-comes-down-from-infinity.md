# Kingman's coalescent comes down from infinity

Let $N_t$ be the number of blocks at time $t$ of [Kingman's coalescent on $\mathbb N$](kingman-coalescent-on-n-as-a-time-indexed-cadlag.md) started
from the partition of $\mathbb N$ into singletons. Then:

1. $N_t < \infty$ for every $t > 0$ almost surely, and $(N_t)_{t > 0}$ is a pure death process with death
   rate $k(k - 1)/2$ from $k$;
2. the time until one block remains has expectation $\sum_{k \ge 2} 2/(k(k - 1)) = 2$;
3. $t N_t \to 2$ almost surely as $t \downarrow 0$.

## Depends on

- [Kingman coalescent on N as a time-indexed cadlag partition process](kingman-coalescent-on-n-as-a-time-indexed-cadlag.md)

## Proof depends on

- [Expected time to the most recent common ancestor of a sample](../kingman-s-coalescent-and-watterson-s-estimator/integral-tmrca.md)

## Expansion

A sound expansion proves (1) from the construction of the process on $\mathbb N$, as in the source. For
(2), let $M_n$ be the time at which the restriction of the process to $\{1, \dots, n\}$ has one block.
Under the restriction coupling $M_n$ is nondecreasing in $n$, and the time until the whole process has one
block is $\sup_n M_n$. Each $M_n$ has the law of a sum of independent $\mathrm{Exp}\binom k2$ variables,
$2 \le k \le n$, so $\mathbb E M_n = 2(1 - 1/n)$, and monotone convergence gives (2). Note that $M_n$ is
not the sum of the holding times of the process on $\mathbb N$ in its states with $2, \dots, n$ blocks: for
$n = 2$ the two sampled individuals merge at one of the jump times of the whole process, not after the
holding time in the state with two blocks. For (3), once (1) holds, the number of blocks of the process on
$\mathbb N$ is a pure death process entering from infinity, whose holding times $T_k$ in the states with
$k$ blocks are independent with $T_k \sim \mathrm{Exp}\binom k2$. The time $\tau_k = \sum_{j > k} T_j$ to reach
$k$ blocks has mean $2/k$ and variance $\sum_{j > k} \binom j2^{-2} = O(k^{-3})$, so $k \tau_k \to 2$ almost
surely (Chebyshev and Borel–Cantelli along $k = j^2$, with monotonicity in between), and inverting
$k \mapsto \tau_k$ gives $t N_t \to 2$. The same limit is the case $\Lambda = \delta_0$ of the
[almost sure asymptotics of the number of blocks of a Λ-coalescent](../multiple-merger-coalescents/speed-of-coming-down-from-infinity/the-number-of-blocks-of-a-coalescent-is-asymptot.md).

## Sources

- J. F. C. Kingman, "The coalescent", Stochastic Processes and their Applications 13 (1982), 235–248, <https://doi.org/10.1016/0304-4149(82)90011-4>, Section 4, Theorem 4 (finitely many classes for $t > 0$ and the death rates).
- S. Tavaré, "Line-of-descent and genealogical processes, and their applications in population genetics models", Theoretical Population Biology 26 (1984), 119–164, <https://doi.org/10.1016/0040-5809(84)90027-3>, Section 6 (the mean $2$ of the time to a single ancestor of the whole population).
- J. Berestycki, N. Berestycki and V. Limic, "The Λ-coalescent speed of coming down from infinity", Annals of Probability 38 (2010), 207–233, <https://doi.org/10.1214/09-AOP475>, preprint <https://arxiv.org/abs/0807.4278>, Section 3, the remark after Theorem 1 ($t N_t \to 2$ for Kingman's coalescent).
