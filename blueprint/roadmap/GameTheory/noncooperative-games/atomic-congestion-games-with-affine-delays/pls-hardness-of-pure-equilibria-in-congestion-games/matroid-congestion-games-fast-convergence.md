# Matroid congestion games converge in polynomially many best responses

In a congestion game in which each player's strategy set is the set of bases of a matroid on the resources (matroid congestion game), every sequence of best responses reaches a pure Nash equilibrium after at most $n^2 m\, \mathrm{rk}$ steps, where $n$ is the number of players, $m$ the number of resources and $\mathrm{rk}$ the maximum rank. With identical delay functions the bound is $n^2\, \mathrm{rk}$. Conversely, the matroid property is the maximal such condition on the individual strategy spaces: for every non-matroid anti-chain $\Sigma$ of resource sets and every $n$ there is a congestion game with $4n$ players, each with a strategy space isomorphic to $\Sigma$, $O(n |R|)$ resources and nonnegative nondecreasing delays, that has a best-response sequence of length $2^n$.

## Proof sketch

Replace every delay value $d_r(i)$ by its rank among the at most $nm$ delay values. By the matroid exchange property, the resources a best response adds and drops can be perfectly matched so that no matched exchange is worse, so a best response that strictly lowers a player's delay also strictly lowers it under the rank delays. Hence Rosenthal's potential for the rank delays, which is at most $n m$ times the number of occupied resource slots, so at most $n^2 m\, \mathrm{rk}$, drops by at least $1$ at every best response. For the converse, a non-matroid anti-chain violates this $(1,1)$-exchange property, and copies of a violating configuration are combined into a game with an exponentially long best-response sequence.

## Depends on

- [Congestion game](../../potential-games/congestion-game.md)
- [Improving move](../../potential-games/improving-move.md)
- [Pure Nash equilibrium](../../potential-games/is-pure-nash.md)

## Proof depends on

- [Finite improvement property](../../potential-games/well-founded-improving-move.md)

## Sources

- H. Ackermann, H. Röglin, B. Vöcking, "On the Impact of Combinatorial Structure on Congestion Games", Journal of the ACM 55(6) (2008); FOCS 2006, Theorems 2.5 and 3.1 and Corollary 3.2.
