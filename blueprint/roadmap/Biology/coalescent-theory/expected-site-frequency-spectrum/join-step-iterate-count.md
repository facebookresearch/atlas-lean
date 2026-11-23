# Expected number of blocks of size $i$

Let $k$, $n$ and $i$ be natural numbers with $2 \le k \le n$ and $1 \le i < n$, let $J$ be the [transition operator of random joining](join-step.md), and let $c_i(b)$ be the number of entries of a list $b$ equal to $i$. Then

$$(J^{n-k} c_i)(1, \dots, 1) = \frac{k \binom{n-i-1}{k-2}}{\binom{n-1}{k-1}},$$

where $(1, \dots, 1)$ is the list of $n$ ones. So for random joining started from $n$ singletons, the expected number of blocks of size $i$ when $k$ blocks remain is $k \binom{n-i-1}{k-2} / \binom{n-1}{k-1}$; equivalently, a block chosen uniformly at random among the $k$ blocks has size $i$ with probability $\binom{n-i-1}{k-2} / \binom{n-1}{k-1}$ (Fu 1995; Griffiths and Tavaré 1998).

## Sources

- Y.-X. Fu, *Statistical properties of segregating sites*, Theoret. Population Biol. 48 (1995), 172–197.
- R. C. Griffiths and S. Tavaré, *The age of a mutation in a general coalescent tree*, Stoch. Models 14 (1998), 273–295.
