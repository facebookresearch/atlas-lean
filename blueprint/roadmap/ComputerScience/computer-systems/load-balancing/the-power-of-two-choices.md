# The power of two choices

For fixed $d \ge 2$, the maximum load achieved by the greedy algorithm on a random [$(n, n, d)$-problem](balls-into-bins-with-d-choices.md) is less than

$$
\frac{\ln \ln n}{\ln d} + O(1)
$$

with high probability, that is, with probability $1 - o(1)$ as $n \to \infty$. Compared with the order $\ln n/\ln \ln n$ for one random choice, a second choice reduces the maximum load exponentially, and further choices only by a constant factor. The proof bounds, by induction on $i$, the number $\beta_i$ of bins with load at least $i$, using $\beta_{i+1} \approx n(\beta_i/n)^d$, so that $\beta_i/n$ decreases doubly exponentially once it is small.

## Depends on

- [Balls into bins with d choices](balls-into-bins-with-d-choices.md)

## Sources

- Y. Azar, A. Z. Broder, A. R. Karlin and E. Upfal, "Balanced allocations", *SIAM Journal on Computing* 29(1):180–200, 1999, Section 3, Theorem 3.2 with its proof, and Section 1, Theorem 1.1 (the general case $m \ge n$ and the comparison with one choice).
