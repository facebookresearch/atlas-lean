# Epsilon-complementary slackness for the assignment problem

For the square assignment problem with costs $c : [n] \times [n] \to \mathbb{Z}$ (minimize $\sum_i c(i, \sigma(i))$ over permutations $\sigma$), let $p : [n] \to \mathbb{Z}$ be **object prices**. A permutation $\sigma$ and prices $p$ satisfy **$\varepsilon$-complementary slackness** ($\varepsilon \ge 0$) if for every person $i$,

$$
c(i, \sigma(i)) + p(\sigma(i)) \le \min_{k} \big(c(i, k) + p(k)\big) + \varepsilon .
$$

The induced row potentials are $u_i = \min_k (c(i,k) + p(k))$.

## Depends on

- [Dual certificate for the assignment problem](../dual-certificate-for-the-assignment-problem.md)

## Sources

- D. P. Bertsekas, "Network Optimization: Continuous and Discrete Models", Athena Scientific, 1998.
- D. P. Bertsekas, "The Auction Algorithm: A Distributed Relaxation Method for the Assignment Problem", Annals of Operations Research 14, 1988.
