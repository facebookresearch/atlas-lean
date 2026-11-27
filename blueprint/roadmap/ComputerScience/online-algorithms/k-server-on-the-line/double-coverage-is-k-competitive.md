# Double Coverage is k-competitive on the line

For $k$ servers on the integer line, Double Coverage satisfies, for every initial configuration $s_0$, every request sequence $\sigma$ and every offline schedule $S$ from $s_0$,

$$
\mathrm{cost}_{\mathrm{DC}}(s_0, \sigma) \le k \cdot \mathrm{cost}(S) + b(s_0),
$$

where the additive term $b(s_0) = \sum_{i<j} |s_{0,i} - s_{0,j}|$ (the initial pairwise spread) depends only on the start, and is $0$ when all servers start at one point. Together with the general lower bound this shows that the deterministic competitive ratio of the $k$-server problem on the line is exactly $k$. For $k \ge 2$, Double Coverage is not $(k, b)$-competitive with a single additive constant $b$ valid for all starting configurations: from servers at $0, 9, 18, \dots, 9(k-1)$, the requests $3, 9, 18, \dots, 9(k-1)$ cost Double Coverage $6k - 3$ against an offline cost of $3$, and scaling the line makes the excess unbounded.

## Proof sketch

Use the potential $\Phi = k \cdot d_{\mathrm{match}}(s_{\mathrm{DC}}, s_{\mathrm{OPT}}) + \sum_{i<j} |s_i - s_j|$. An offline move of length $\ell$ raises $\Phi$ by at most $k \ell$. If Double Coverage moves one outer server by $\delta$, the matching term drops by $k\delta$ and the spread grows by $(k-1)\delta$; if it moves two inner servers by $\delta$ each toward the request, the matching term does not grow and the spread drops by $2\delta$. In both cases $\mathrm{cost}_{\mathrm{DC}} + \Delta\Phi \le k \cdot \mathrm{cost}_{\mathrm{OPT}}$, and telescoping gives the bound.

## Depends on

- [Double Coverage algorithm on the line](double-coverage-algorithm.md)
- [Matching distance between server configurations](matching-distance-between-configurations.md)
- [Online request-serving problem and competitive ratio](../competitive-analysis/online-problem-and-competitive-ratio.md)

## Proof depends on

- [Potential method: amortized costs bound actual costs](../../data-structures/amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- M. Chrobak, H. J. Karloff, T. H. Payne and S. Vishwanathan, "New Results on Server Problems", SIAM Journal on Discrete Mathematics 4(2), 1991.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
