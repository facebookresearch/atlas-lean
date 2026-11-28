# Linear-programming characterization of the classical secretary problem

For the classical secretary problem with $n$ candidates and no advice, the optimal win probability equals the value of the linear program $\max \sum_{i=1}^n \frac{i}{n} x_i$ subject to $x_i \le \frac{1}{i}\big(1 - \sum_{j < i} x_j\big)$ and $x_i \ge 0$, where $x_i$ is the probability that the algorithm accepts the $i$-th candidate and that candidate is the best so far. The optimum is attained by a threshold rule and tends to $1/e$.

## Proof sketch

Any policy induces such $x$: the $i$-th candidate is the best so far with probability $1/i$ independently of the earlier relative ranks, and the policy can accept it only if it has not stopped before, which gives the constraint; accepting a best-so-far candidate at position $i$ wins with probability $i/n$. Conversely, every feasible $x$ is realized by a randomized policy accepting a best-so-far candidate at position $i$ with probability $i x_i/(1 - \sum_{j < i} x_j)$. LP duality shows that an optimal solution is zero up to about $n/e$ and tight afterwards.

## Depends on

- [Secretary problems with advice](secretary-with-advice-model.md)

## Proof depends on

- [Strong linear programming duality](../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- Niv Buchbinder, Kamal Jain, Mohit Singh, "Secretary Problems via Linear Programming", Mathematics of Operations Research 39(1) (2014); IPCO (2010).
- Paul Dütting, Silvio Lattanzi, Renato Paes Leme, Sergei Vassilvitskii, "Secretaries with Advice", EC (2021); Mathematics of Operations Research 49(2) (2024), arXiv:2011.06726.
