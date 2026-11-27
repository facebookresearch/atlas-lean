# No conditional regret characterises correlated equilibria

After $T \ge 1$ rounds, the empirical distribution of play is a correlated
$\varepsilon$-equilibrium if and only if every conditional regret is at most $T\varepsilon$,
that is, every average regret $D_T(j, k)$ is at most $\varepsilon$. This is the finite-horizon
form of Hart and Mas-Colell's Proposition: $\limsup_T R_T(j, k) \le \varepsilon$ for all
players and $j \ne k$ if and only if $z_T$ converges to the set of correlated
$\varepsilon$-equilibria. The limit form also uses the compactness of the simplex.

## Informally uses

- [Conditional regrets are linear in the empirical distribution](cond-regret-div-eq.md): the
  identity behind the equivalence.

## Background

- [No-regret dynamics converge to coarse correlated equilibria](../no-regret-dynamics/is-coarse-correlated-eq-empirical.md):
  the unconditional analogue.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §3, Proposition.
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §10.8.
