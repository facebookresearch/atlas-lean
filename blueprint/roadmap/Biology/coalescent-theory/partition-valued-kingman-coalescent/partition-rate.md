# Rate matrix of Kingman's partition-valued coalescent

For a natural number $n$, the rate matrix $Q_n$ of Kingman's partition-valued coalescent is the real matrix indexed by $\mathcal{P}_n \times \mathcal{P}_n$ with $Q_n(\pi, \pi') = 1$ if $\pi'$ [arises from $\pi$ by merging two blocks](is-merge.md), $Q_n(\pi, \pi) = -\binom{|\pi|}{2}$, and $Q_n(\pi, \pi') = 0$ otherwise. Each pair of blocks merges at rate $1$, so a partition with $k$ blocks is left at total rate $\binom{k}{2}$, with time in units of $2N$ generations.
