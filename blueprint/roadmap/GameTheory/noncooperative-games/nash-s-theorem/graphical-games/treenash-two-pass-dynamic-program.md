# TreeNash two-pass dynamic program

Let $M$ be a graphical game whose graph is a tree rooted at $r$. Orient edges towards $r$, so each $v \ne r$ has a unique downstream neighbour $w$ and upstream neighbours $U_1, \dots, U_k$. In the *downstream pass*, processed from the leaves, each $v$ computes the table $T(w, v)$ of pairs of mixed strategies $(x_w, x_v)$ such that $x_v$ is a best response to $x_w$ and some upstream strategies $x_{U_1}, \dots, x_{U_k}$ with $T(v, U_j)(x_v, x_{U_j})$ all true, recording witnesses. In the *upstream pass*, the root chooses $x_r$ together with strategies $x_{U_1}, \dots, x_{U_k}$ of its upstream neighbours such that $T(r, U_j)(x_r, x_{U_j})$ holds for every $j$ and $x_r$ is a best response to $x_{U_1}, \dots, x_{U_k}$ (equivalently, Kearns' one-dimensional root table $T(x_r)$ is true at $x_r$), and each node instantiates its upstream neighbours from the recorded witnesses.

## Depends on

- [Graphical game](graphical-game.md)
- [Mixed Nash equilibrium](../is-mixed-nash.md)

## Sources

- Michael Kearns, "Graphical Games", Algorithmic Game Theory, Cambridge University Press, 2007.
