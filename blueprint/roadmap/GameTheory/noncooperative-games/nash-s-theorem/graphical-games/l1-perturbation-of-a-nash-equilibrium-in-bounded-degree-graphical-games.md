# L1 perturbation of a Nash equilibrium in bounded-degree graphical games

Let $M$ be a graphical game with local payoffs in $[0, 1]$ and maximum degree at most $d$. If $p$ is a mixed Nash equilibrium and $q$ is a mixed profile with $\|q_j - p_j\|_1 \le \tau$ for every player $j$, then $q$ is an additive $(d\tau)$-approximate Nash equilibrium (for binary actions; for general finite actions the slack is proportional to $d \tau$ with the same structure).

## Proof sketch

Player $i$'s expected payoff depends on the $d$ neighbours' mixed strategies multilinearly with coefficients in $[0,1]$; changing one neighbour's strategy by $\tau$ in $L^1$ changes it by at most $\tau/2$, and summing over neighbours and comparing the equilibrium and deviation payoffs gives the bound.

## Depends on

- [Graphical game](graphical-game.md)
- [Additive approximate Nash equilibrium](../approximate-and-symmetric-equilibria/additive-approximate-nash-equilibrium.md)

## Sources

- Michael Kearns, "Graphical Games", Algorithmic Game Theory, Cambridge University Press, 2007.
