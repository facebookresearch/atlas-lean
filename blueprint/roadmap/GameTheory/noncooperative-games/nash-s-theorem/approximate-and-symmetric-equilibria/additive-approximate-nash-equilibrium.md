# Additive approximate Nash equilibrium

Let $\varepsilon \ge 0$. In a finite cost-minimization game, a mixed profile $x$ is an *$\varepsilon$-approximate Nash equilibrium* if for every player $i$ and every pure strategy $a \in S_i$, $E_i(x) \le C_i(x; a) + \varepsilon$, where $E_i(x)$ is player $i$'s expected cost and $C_i(x; a)$ its expected cost after deviating to $a$. For a bimatrix game with payoff matrices $A, B$ (maximized), $(x, y)$ is an $\varepsilon$-approximate Nash equilibrium if $x^\top A y \ge e_i^\top A y - \varepsilon$ for every row $i$ and $x^\top B y \ge x^\top B e_j - \varepsilon$ for every column $j$. For $\varepsilon = 0$ both notions are mixed Nash equilibria.

## Depends on

- [Mixed Nash equilibrium](../is-mixed-nash.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)

## Sources

- Christos H. Papadimitriou, "The Complexity of Finding Nash Equilibria", Algorithmic Game Theory, Cambridge University Press, 2007.
- Michael Kearns, "Graphical Games", Algorithmic Game Theory, Cambridge University Press, 2007.
