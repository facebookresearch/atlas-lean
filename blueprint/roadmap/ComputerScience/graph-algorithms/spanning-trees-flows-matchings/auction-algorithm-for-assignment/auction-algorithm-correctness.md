# Termination and near-optimality of the auction algorithm

Let $C$ bound the cost differences, $c(i, k) - c(i, j) \le C$ for all $i, j, k$. The auction algorithm with parameter $\varepsilon > 0$ maintains $\varepsilon$-complementary slackness for the partial assignment, terminates after at most $n(C + \varepsilon)/\varepsilon$ bids, and returns a complete assignment whose cost is within $n\varepsilon$ of optimal. The scaled version returns an optimal assignment. Adding a constant to all costs does not change the bids or the output.

## Proof sketch

Each bid satisfies slackness for the bidder and preserves it for others since prices only rise. The measure $n(C + \varepsilon) - \sum_j p_j$ is nonnegative while some person is unassigned and drops by at least $\varepsilon$ per bid. Near-optimality is the slackness lemma.

## Depends on

- [Bertsekas's Gauss-Seidel auction algorithm](gauss-seidel-auction-algorithm.md)

## Proof depends on

- [Epsilon-complementary slackness implies near-optimality](epsilon-cs-near-optimality.md)

## Sources

- D. P. Bertsekas, "The Auction Algorithm: A Distributed Relaxation Method for the Assignment Problem", Annals of Operations Research 14, 1988.
- D. P. Bertsekas, "Network Optimization: Continuous and Discrete Models", Athena Scientific, 1998.
