# L1 perturbation of a Nash equilibrium in bounded-degree graphical games

Let $M$ be a graphical game with finite action sets and local payoffs in $[0, 1]$ in which each player's payoff depends on the actions of at most $d$ players, itself included. If $p$ is a mixed Nash equilibrium and $q$ is a mixed profile with $\|q_j - p_j\|_1 \le \tau$ for every player $j$, then $q$ is an additive $(d\tau)$-approximate Nash equilibrium.

## Proof sketch

Player $i$'s expected payoff is multilinear in the mixed strategies of the at most $d$ players it depends on, with coefficients in $[0,1]$; changing one of them by $\tau$ in $L^1$ changes it by at most $\tau/2$. So at $q$ every pure deviation of $i$ gains at most $(d-1)\tau/2$ over its value at $p$, which is at most $i$'s equilibrium payoff, and $i$'s payoff at $q$ is at most $d\tau/2$ below its equilibrium payoff; the total is at most $(2d-1)\tau/2 \le d\tau$.

## Depends on

- [Graphical game](graphical-game.md)
- [Additive approximate Nash equilibrium](../approximate-and-symmetric-equilibria/additive-approximate-nash-equilibrium.md)

## Sources

- Michael Kearns, "Graphical Games", Algorithmic Game Theory, Cambridge University Press, 2007.
