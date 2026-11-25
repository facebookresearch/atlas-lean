# Expected total age of mutations of a given size in Kingman's coalescent

Take Kingman's coalescent on $n \ge 2$ leaves. Let $T_k$ be the time it has $k$ lineages, $V_{k+1} = \sum_{j > k} T_j$ the time at which that period starts, and $c_k = \binom{k}{2}$. Mutations fall on the branches as a Poisson process of intensity $\theta/2$ per unit length, under the infinite-sites model, independently of the topology and the holding times. A mutation is of size $i$ if it is carried by exactly $i$ leaves, $1 \le i \le n - 1$, and its age is its distance from the present.

A mutation on one of the $k$ branches of period $k$ falls at time $V_{k+1} + U T_k$ with $U$ uniform on $[0, 1]$. That branch subtends exactly $i$ leaves with probability $\binom{n-i-1}{k-2} \big/ \binom{n-1}{k-1}$. Hence the expected sum of the ages of the size-$i$ mutations is

$$\mathbb{E}\Bigl[\sum_{\text{size-}i\text{ mutations}} \text{age}\Bigr] = \frac{\theta}{2} \sum_{k=2}^{n-i+1} k\, \frac{\binom{n-i-1}{k-2}}{\binom{n-1}{k-1}} \Bigl(\frac{1}{c_k} \sum_{j=k+1}^{n} \frac{1}{c_j} + \frac{1}{c_k^2}\Bigr).$$

Dividing by the [expected number of size-$i$ mutations](integral-sfs.md), $\mathbb{E}\,\xi_i = \theta / i$, gives the mean age of a size-$i$ mutation in the sense of Campbell's formula. The same weights without the age factor give $\theta / i$.

## Depends on

- [Expected site frequency spectrum](integral-sfs.md)

## Proof depends on

- [Poisson point process with finite intensity](../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md)

## Expansion

1. The time of a mutation on a period-$k$ branch, from the Poisson construction conditional on the genealogy.
2. The weight $k \binom{n-i-1}{k-2} / \binom{n-1}{k-1}$, from the independence of the topology and the holding times.
3. The moments $\mathbb{E}[T_k] = 1/c_k$, $\mathbb{E}[T_k^2] = 2/c_k^2$ and the independence of $T_k$ from $V_{k+1}$, which give the bracket.
4. The checks: for $n = 2$, $i = 1$ the total is $\theta$ and the mean age is $1$. For $n = 3$, $i = 1$ the total is $5\theta/6$.

## Sources

- R. C. Griffiths and S. Tavaré, The age of a mutation in a general coalescent tree, *Comm. Statist. Stochastic Models* 14 (1998), 273–295 (age of a mutation; motivation).
- Y.-X. Fu, Statistical properties of segregating sites, *Theor. Popul. Biol.* 48 (1995), 172–197 (branch classes).
