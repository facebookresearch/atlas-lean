# Strong equilibria of fair cost-sharing games cost at most H_k times the optimum

Let $G$ be a fair connection game with $k$ players on a directed graph with nonnegative edge costs, and let $H_k = \sum_{j=1}^k 1/j$. Every strong equilibrium $s$ of $G$ satisfies $C(s) \le H_k \cdot C(s^*)$ for every profile $s^*$, where $C$ denotes the total cost of the edges in use. This bounds every strong equilibrium; strong equilibria need not exist.

## Proof sketch

Order the players so that, starting from the coalition of all players, at each step some player of the remaining coalition does not strictly gain by jointly switching to $s^*$. Removing players one at a time and charging each its share in $s^*$ when $j$ players remain gives a cost bound of $c_e/j$ per edge, which sums to at most $H_k$ times $C(s^*)$.

## Depends on

- [Strong equilibrium, strong Nash equilibrium and k-resilience](strong-equilibrium-strong-nash-equilibrium-and-k-resilience.md)
- [Fair connection game on a network](../../atomic-congestion-games-with-affine-delays/atomic-congestion-efficiency/fair-connection-game-on-a-network.md)

## Proof depends on

- [Rosenthal's potential for fair cost sharing](../fair-cost-sharing-potential-eq.md)

## Sources

- Amir Epstein, Michal Feldman and Yishay Mansour, "Strong Equilibrium in Cost Sharing Connection Games", Games and Economic Behavior 67 (2009), 51–68, Theorem 3.7 (the strong price of anarchy of a fair connection game with $n$ players is at most $H(n)$) and Theorem 3.6 (fair connection games without a strong equilibrium exist).
- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
