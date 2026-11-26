# Proportion of trees sharing k splits with a fixed tree

**Setting.** Let $UB(n)$ be the set of unrooted binary phylogenetic trees on $n$ labelled leaves, so $|UB(n)|=(2n-5)!!$. A split of a tree is the bipartition of the leaves obtained by deleting one edge; it is non-trivial if both parts have at least two leaves, and a binary tree with $n$ leaves has $i_0=n-3$ non-trivial splits.

**Theorem.** Let $T_0$ be any phylogenetic tree on $n$ leaves with $i_0$ internal edges, and let $\pi_k(T_0)$ be the proportion of trees in $UB(n)$ that share at least $k$ non-trivial splits with $T_0$. Then

$$\pi_k(T_0)\le\frac{1}{2^k\,k!}\qquad\text{for }k=1,2,\dots,i_0,$$

and $\pi_k(T_0)=0$ for $k>i_0$.

In particular, a uniformly random binary tree shares even one non-trivial split with a fixed tree with probability at most $1/2$, and the probability of sharing many splits decays faster than exponentially in $k$, uniformly in $n$.

## Expansion

Write $N_k(T_0)$ for the number of binary trees sharing at least $k$ non-trivial splits with $T_0$. By the union bound over the $\binom{i_0}{k}$ sets $\Sigma$ of $k$ splits of $T_0$, $N_k(T_0)\le\binom{i_0}{k}M$, where $M$ is the largest number of binary trees displaying a given $\Sigma$. Contracting every other internal edge of $T_0$ gives a tree $T_\Sigma$ with exactly $k+1$ interior vertices whose degrees sum to $n+2k$, and the binary trees displaying $\Sigma$ are the independent binary resolutions of its interior vertices, so their number is $\prod_{v}|UB(\deg v)|=\prod_v(2\deg v-5)!!$. Maximizing this product under the degree constraints and dividing by $|UB(n)|=(2n-5)!!$, then using $i_0\le n-3$, gives the bound $1/(2^k k!)$. A tree cannot share more non-trivial splits than $T_0$ has, which gives the vanishing for $k>i_0$.

## Sources

- Jamie V. de Jong, Jeanette C. McLeod, Mike Steel, "Neighbourhoods of phylogenetic trees: exact and asymptotic counts", arXiv:1508.03774 (2015): Section 3, subsection "Shared Splits" (the theorem bounding $\pi_k(T_0)$). <https://doi.org/10.48550/arXiv.1508.03774> Published version: SIAM Journal on Discrete Mathematics 30 (2016) 2265–2287, <https://doi.org/10.1137/15m1035070>.
