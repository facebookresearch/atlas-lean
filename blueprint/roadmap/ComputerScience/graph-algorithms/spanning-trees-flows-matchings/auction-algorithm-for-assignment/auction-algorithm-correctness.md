# Termination and near-optimality of the auction algorithm

The auction algorithm with parameter $\varepsilon > 0$ maintains $\varepsilon$-complementary slackness for the partial assignment, terminates after finitely many bids, and returns a complete assignment whose cost is within $n\varepsilon$ of optimal (Bertsekas 1988, Propositions 1 and 2; Bertsekas 1998, Propositions 7.1 and 7.2). For integer costs the scaled version returns an optimal assignment, since it runs with $\varepsilon = 1/(n+1) < 1/n$ in the original units.

## Proof sketch

Each bid satisfies slackness for the bidder and preserves it for others since prices only rise. Near-optimality is the slackness lemma. A bid count follows: let $C$ bound the cost differences, $c(i, k) - c(i, j) \le C$ for all $i, j, k$. Before every bid but the last, some object other than the one bid for has never received a bid and has price $0$, so the new price $w - c(i, j) + \varepsilon$ is at most $C + \varepsilon$. As each bid raises the sum of prices by at least $\varepsilon$ and that sum stays at most $(n-1)(C + \varepsilon)$ before the last bid, there are at most $n(C + \varepsilon)/\varepsilon$ bids. Adding a constant to all costs shifts every reduced cost equally, so it changes neither the bids nor the output.

## Depends on

- [Bertsekas's Gauss-Seidel auction algorithm](gauss-seidel-auction-algorithm.md)

## Proof depends on

- [Epsilon-complementary slackness implies near-optimality](epsilon-cs-near-optimality.md)

## Sources

- D. P. Bertsekas, "The Auction Algorithm: A Distributed Relaxation Method for the Assignment Problem", Annals of Operations Research 14, 1988.
- D. P. Bertsekas, "Network Optimization: Continuous and Discrete Models", Athena Scientific, 1998.
