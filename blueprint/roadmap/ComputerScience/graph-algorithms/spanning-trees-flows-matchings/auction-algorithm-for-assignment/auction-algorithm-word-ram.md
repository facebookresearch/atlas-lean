# The auction algorithm on the word RAM

There are deterministic word-RAM programs that, given an $n \times n$ signed integer cost matrix with entries of absolute value at most $M$, run the $\varepsilon$-auction (returning an assignment within $n\varepsilon$ of optimal) and the scaled auction (returning an optimal assignment and its cost) at word sizes holding the scaled prices, using $O(n^2)$ instructions of initialization and $O(n)$ instructions per bid, since a bid scans the $n$ objects once for the best and second-best reduced costs (Bertsekas 1988, Eqs. (5)-(7); Bertsekas 1998, Section 7.1, bid calculation).

## Proof sketch

The correctness page gives termination; the number of bids is bounded as follows. The cost differences satisfy $c(i, k) - c(i, j) \le C$ with $C = 2M$. Before every bid but the last, some object other than the one bid for has never received a bid and so still has price $0$; for that object $k$ the second smallest reduced cost satisfies $w \le c(i, k)$, so the new price $w - c(i, j) + \varepsilon$ is at most $c(i, k) - c(i, j) + \varepsilon \le C + \varepsilon$. Prices never decrease, each bid raises the sum of prices by at least $\varepsilon$, and before the last bid that sum is at most $(n - 1)(C + \varepsilon)$, so there are at most $n(C + \varepsilon)/\varepsilon$ bids. In the scaled version the costs are multiplied by $n + 1$ and $\varepsilon = 1$, so $C \le 2M(n+1)$. The total is $O\big(n^2 + n \cdot \tfrac{n(C+\varepsilon)}{\varepsilon}\big)$ instructions.

## Depends on

- [Bertsekas's Gauss-Seidel auction algorithm](gauss-seidel-auction-algorithm.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Termination and near-optimality of the auction algorithm](auction-algorithm-correctness.md)

## Sources

- D. P. Bertsekas, "The Auction Algorithm: A Distributed Relaxation Method for the Assignment Problem", Annals of Operations Research 14, 1988.
- D. P. Bertsekas, "Network Optimization: Continuous and Discrete Models", Athena Scientific, 1998.
