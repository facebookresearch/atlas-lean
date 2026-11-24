# Jump chain of Kingman's coalescent

For a natural number $n$, the jump matrix $J_n$ of Kingman's coalescent is the real matrix indexed by $\mathcal{P}_n \times \mathcal{P}_n$ with entries

- $J_n(\pi, \pi') = \binom{|\pi|}{2}^{-1}$ if $|\pi| \ge 2$ and $\pi'$ [arises from $\pi$ by merging two blocks](is-merge.md), and $0$ for the other $\pi'$ when $|\pi| \ge 2$;
- $J_n(\pi, \pi') = 1$ if $\pi' = \pi$ and $0$ otherwise, when $|\pi| \le 1$.

So from a partition with $k \ge 2$ blocks the chain moves to each of the $\binom{k}{2}$ partitions obtained by merging two blocks with probability $1/\binom{k}{2}$, and a partition with at most one block is absorbing.
