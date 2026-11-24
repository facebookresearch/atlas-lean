# Correlated equilibrium

A probability distribution $\psi$ on the strategy profiles of a finite game with costs $c_i$ is a
correlated $\varepsilon$-equilibrium if for every player $i$ and all strategies $j, k$ of $i$

$$\sum_{s :\, s_i = j} \psi(s)\,\bigl(c_i(s) - c_i(k, s_{-i})\bigr) \le \varepsilon,$$

and a correlated equilibrium when $\varepsilon = 0$. Think of a referee who draws $s$ from
$\psi$ and tells each player only its own coordinate $s_i$: a player told to play $j$ cannot gain
by playing $k$ instead, provided the others obey. With payoffs $u_i = -c_i$ this is the
definition of Hart and Mas-Colell; Aumann introduced the notion as a Nash equilibrium of the game
extended by payoff-irrelevant correlated signals.

The error is additive and summed over the event $\{s_i = j\}$, as in Hart and Mas-Colell; it is
not divided by the probability of that event.

## Background

- [Coarse correlated equilibrium](../no-regret-dynamics/is-coarse-correlated-eq.md): the weaker
  notion where a player may only commit in advance to a fixed deviation.
- [Mixed Nash equilibrium](../nash-s-theorem/is-mixed-nash.md): the equilibria with independent
  randomisation, which are the product correlated equilibria.

## Sources

- S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium", Econometrica 68(5) (2000), 1127–1150, §2, Definition (payoff form).
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §6, inequality (6).
- R. J. Aumann, "Subjectivity and correlation in randomized strategies", J. Math. Econom. 1 (1974), 67–96.
