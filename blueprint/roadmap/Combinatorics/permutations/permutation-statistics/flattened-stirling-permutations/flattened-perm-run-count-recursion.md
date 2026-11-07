# Recursion for flattened partitions by number of runs

Let $f_{n,k}$ be the number of
flattened partitions of length $n$ with exactly $k$ runs. For all $n \ge 1$ and $k \ge 2$,

$$
f_{n,k} = \sum_{m=1}^{n-2} \left( \binom{n-1}{m} - 1 \right) f_{m,k-1},
$$

where the sum is empty when $n \le 2$. Moreover $f_{n,1} = 1$ for every $n \ge 1$, and
$f_{n,k} = 0$ whenever $2 \le n \le k$.

This is the recursion of Nabawanda, Rakotondrajao, and Bamunoba as quoted in the paper.

## Sources

- Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling Permutations*, INTEGERS 24 (2024), Article A104, Theorem 1 (quoting Nabawanda et al., Theorem 1).
