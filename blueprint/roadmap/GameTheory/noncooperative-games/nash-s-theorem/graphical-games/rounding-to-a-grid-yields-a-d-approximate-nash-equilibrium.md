# Rounding to a τ-grid yields a dτ-approximate Nash equilibrium

Let $M$ be a binary-action graphical game with local payoffs in $[0, 1]$ in which each player's payoff depends on the actions of at most $d$ players, itself included, let $p$ be an exact mixed Nash equilibrium and $m \ge 1$. Rounding each $p_i$ to the nearest point of the grid $\{0, 1/m, \dots, 1\}$ changes each strategy by at most $1/m$ in $L^1$, and the rounded profile is an additive $(d/m)$-approximate Nash equilibrium. Hence ApproximateTreeNash on the grid finds an $\varepsilon$-approximate equilibrium of a tree graphical game with grid resolution $\tau = \varepsilon/d$.

## Proof sketch

Apply the perturbation lemma with $\tau = 1/m$ to the rounding of an exact equilibrium; the grid version of TreeNash then searches a finite table that contains this rounded profile.

## Depends on

- [L1 perturbation of a Nash equilibrium in bounded-degree graphical games](l1-perturbation-of-a-nash-equilibrium-in-bounded-degree-graphical-games.md)
- [TreeNash two-pass dynamic program](treenash-two-pass-dynamic-program.md)

## Proof depends on

- [TreeNash computes and represents all Nash equilibria of tree graphical games](treenash-computes-and-represents-all-nash-equilibria-of-tree-graphical-games.md)

## Sources

- Michael Kearns, "Graphical Games", Algorithmic Game Theory, Cambridge University Press, 2007.
