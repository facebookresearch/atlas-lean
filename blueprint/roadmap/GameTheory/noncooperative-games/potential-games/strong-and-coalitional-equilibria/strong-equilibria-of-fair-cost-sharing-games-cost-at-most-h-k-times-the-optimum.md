# Strong equilibria of fair cost-sharing games cost at most H_k times the optimum

Let $G$ be a $k$-player fair cost-sharing game with nonnegative resource costs, and let $H_k = \sum_{j=1}^k 1/j$. Every strong equilibrium $s$ of $G$ (and hence every strong Nash equilibrium) satisfies $C(s) \le H_k \cdot C(s^*)$ for every profile $s^*$, where $C$ denotes the total cost of the resources in use. This bounds every strong equilibrium; strong equilibria need not exist in general.

## Proof sketch

Order the players so that, starting from the coalition of all players, at each step some player of the remaining coalition does not strictly gain by jointly switching to $s^*$. Removing players one at a time and charging each its share in $s^*$ when $j$ players remain gives a cost bound of $c_e/j$ per resource, which sums to at most $H_k$ times $C(s^*)$.

## Depends on

- [Strong equilibrium, strong Nash equilibrium and k-resilience](strong-equilibrium-strong-nash-equilibrium-and-k-resilience.md)
- [Fair cost-sharing game](../fair-cost-sharing.md)

## Proof depends on

- [Rosenthal's potential for fair cost sharing](../fair-cost-sharing-potential-eq.md)

## Sources

- Amir Epstein, Michal Feldman and Yishay Mansour, "Strong Equilibrium in Cost Sharing Connection Games", Games and Economic Behavior, 2009.
- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
