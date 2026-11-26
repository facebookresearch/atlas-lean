# Expected number of jumps of jump consistent hash

For the idealized [jump consistent hash](jump-consistent-hash.md) with $n \ge 2$ buckets, the expected number of jump destinations below $n$ is $\sum_{i=2}^{n} 1/i$, which is less than $\ln n$, since there is a jump at $j$ with probability $1/(j+1)$. The algorithm that generates the jump destinations directly performs one iteration per destination below $n$ plus one, so its expected number of iterations is less than $\ln n + 1$.

## Depends on

- [Jump consistent hash](jump-consistent-hash.md)

## Proof depends on

- [Next jump destination of jump consistent hash](next-jump-destination-of-jump-consistent-hash.md): the algorithm visits exactly the jump destinations.

## Sources

- J. Lamping and E. Veach, "A fast, minimal memory, consistent hash algorithm", arXiv:1406.2294, 2014, <https://arxiv.org/abs/1406.2294>, section "Performance Analysis".
