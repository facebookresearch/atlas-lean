# Replicable approximate medians over finite ordered domains

A randomized algorithm $A(S; r)$ taking an i.i.d. sample $S$ from a distribution $D$ and internal randomness $r$ is **$\rho$-replicable** if $\Pr_{S, S' \sim D^n,\, r}[A(S; r) = A(S'; r)] \ge 1 - \rho$ for every $D$, where $S, S', r$ are independent and the same $r$ is used in both runs. Let $X$ be a well-ordered domain of size $2^d$ and call $x$ a $\tau$-approximate median of $D$ if $\Pr_{x' \sim D}[x' \le x] \ge \tfrac12 - \tau$ and $\Pr_{x' \sim D}[x' \ge x] \ge \tfrac12 - \tau$. There is a $\rho$-replicable algorithm that outputs a $\tau$-approximate median with probability at least $1 - \rho/2$ using

$$
\tilde O\!\left(\frac{1}{\tau^2 \rho^2} \cdot \Big(\frac{3}{\tau^2}\Big)^{\log^* |X|}\right)
$$

samples. Applied to the output distribution of a mildly accurate algorithm whose correct answers form an interval, a replicable approximate median yields an accurate replicable algorithm.

## Proof sketch

Replace $D$ by the distribution $D_m$ of non-replicable empirical medians of small subsamples, each a $\tau$-approximate median of $D$ with high probability, so that any element of the prefix tree carrying constant $D_m$-mass yields a $\tau$-approximate median of $D$. Pair up such medians and let $\ell$ be the longest common prefix of a pair; a replicable approximate median of this prefix-length distribution, over a domain of size $2^{\lceil \log d \rceil} = \Theta(d)$, is found by recursion. At levels $\ell$ and $\ell + 1$ of the binary prefix tree, the replicable heavy-hitters algorithm run on the length-$\ell$ and length-$(\ell+1)$ prefixes of fresh medians returns the list of heavy prefixes (weight about $1/4$ or more); each listed prefix $v$ is then tested by a replicable statistical query for the $D_m$-probability of having prefix $v$, a prefix of weight in $[1/4, 3/4]$ is kept, and it is padded with all $0$s or all $1$s to length $d$, as decided by one more replicable statistical query. The recursion depth is $\log^* |X|$, and each level loses a factor $O(1/\tau^2)$ in samples and a constant factor in accuracy. Replicability of each level comes from the heavy-hitters step and from randomized rounding of empirical statistics with shared offsets.

## Depends on

- [Replicable algorithms with shared randomness](../../../replicable-learning/replicable-algorithms-with-shared-seed.md)

## Proof depends on

- [Replicable bounded-mean and coin-bias estimation](../../../replicable-learning/replicable-mean-estimation.md)
- [Replicable heavy hitters with domain-independent sample complexity](replicable-heavy-hitters.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi, J. Sorrell, "Reproducibility in Learning", STOC (2022), arXiv:2201.08430, Definition 4.1, Theorems 4.2 and 4.8 and Algorithm 3.
