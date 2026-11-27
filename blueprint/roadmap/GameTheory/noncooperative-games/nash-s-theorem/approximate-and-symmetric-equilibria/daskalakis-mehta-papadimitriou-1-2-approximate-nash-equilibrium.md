# Daskalakis–Mehta–Papadimitriou 1/2-approximate Nash equilibrium

Let $(A, B)$ be a bimatrix game with payoffs in $[0, 1]$. Fix any row $i_0$, let $j_0$ be a pure best response of the column player to $i_0$, and let $i_1$ be a pure best response of the row player to $j_0$. Then the pair $\bigl(\tfrac12 e_{i_0} + \tfrac12 e_{i_1},\ e_{j_0}\bigr)$ is a $\tfrac12$-approximate Nash equilibrium. In particular every such game has a $\tfrac12$-approximate equilibrium with supports of size at most two and one.

## Proof sketch

The row player loses at most $\tfrac12$ because half its mass is on a best response to $j_0$ and payoffs lie in $[0,1]$. The column player's payoff from $e_{j_0}$ against $e_{i_0}$ is maximal, so any deviation gains at most the payoff against $e_{i_1}$, scaled by $\tfrac12$.

## Depends on

- [Additive approximate Nash equilibrium](additive-approximate-nash-equilibrium.md)

## Sources

- Constantinos Daskalakis, Aranyak Mehta and Christos H. Papadimitriou, "A Note on Approximate Nash Equilibria", Internet and Network Economics (WINE 2006), 2006.
- Christos H. Papadimitriou, "The Complexity of Finding Nash Equilibria", Algorithmic Game Theory, Cambridge University Press, 2007.
