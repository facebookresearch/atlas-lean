# Polylogarithmic swap regret and near-optimal convergence to correlated equilibria

In a finite $m$-player general-sum game with $n$ actions per player and losses in $[0, 1]$, if every player runs the Blum–Mansour stationary-distribution construction with Optimistic Hedge as each internal external-regret learner, then every player's swap regret after $T$ rounds is $O\bigl(\mathrm{poly}(m, \log n) \cdot \mathrm{polylog}\, T\bigr)$. Consequently the empirical distribution of joint play is an $\tilde O(1/T)$-approximate correlated equilibrium, which is optimal within no-regret dynamics up to polylogarithmic factors.

## Proof sketch

The stationary distribution $x^t$ is a fixed point of the matrix $Q^t$ built from the optimistic learners' iterates. Using a Markov chain tree theorem representation of the stationary distribution as a ratio of polynomials in the entries of $Q^t$, one shows that higher-order smoothness of the learners' iterates transfers to $x^t$. Then the polylogarithmic-regret machinery for Optimistic Hedge applies to each learner's scaled loss sequence, and the swap regret is the sum of the $n$ learners' external regrets.

## Depends on

- [Internal and swap regret minimization via stationary distributions](swap-regret-stationary-distribution-dynamics.md)
- [Correlated equilibrium](../../correlated-equilibria/is-correlated-eq.md)
- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Proof depends on

- [Optimistic Hedge achieves polylogarithmic individual regret in general-sum games](optimistic-hedge-polylog-regret.md)
- [No-swap-regret dynamics converge to correlated equilibria](../../no-regret-dynamics/no-swap-regret-dynamics-converge-to-correlated-equilibria.md)
- [Higher-order smoothness of Optimistic Hedge iterates](higher-order-smoothness-optimistic-hedge.md)

## Sources

- I. Anagnostides, C. Daskalakis, G. Farina, M. Fishelson, N. Golowich, T. Sandholm, "Near-Optimal No-Regret Learning for Correlated Equilibria in Multi-Player General-Sum Games", STOC 2022, arXiv:2111.06008.
