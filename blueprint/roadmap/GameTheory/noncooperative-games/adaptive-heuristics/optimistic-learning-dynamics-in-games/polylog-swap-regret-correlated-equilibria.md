# Polylogarithmic swap regret and near-optimal convergence to correlated equilibria

In a finite $m$-player general-sum game with $n$ actions per player and losses in $[0, 1]$, if every player runs the Blum–Mansour stationary-distribution construction with Optimistic Hedge as each internal external-regret learner, with step size $\eta = 1/(C m n^3 \log^4 T)$ for a suitable constant $C$, then every player's swap regret after $T$ rounds is $O(m n^4 \log n \log^4 T)$. Consequently the average of the product distributions of play is an $O(m n^4 \log n \log^4 T / T)$-approximate correlated equilibrium, which is optimal within no-regret dynamics up to polylogarithmic factors in $T$. (The Stoltz–Lugosi variant achieves internal regret $O(m \log n \log^4 T)$, hence swap regret $O(m n \log n \log^4 T)$.)

## Proof sketch

The stationary distribution $x^t$ is a fixed point of the matrix $Q^t$ built from the optimistic learners' iterates. Using the Markov chain tree theorem, which writes the stationary distribution as a ratio of polynomials in the entries of $Q^t$, together with the Cauchy integral formula to bound higher derivatives of this map, one shows that higher-order smoothness of the learners' iterates transfers to $x^t$. Then the polylogarithmic-regret machinery for Optimistic Hedge applies to each learner's scaled loss sequence, and the swap regret is the sum of the $n$ learners' external regrets.

## Depends on

- [Internal and swap regret minimization via stationary distributions](swap-regret-stationary-distribution-dynamics.md)
- [Correlated equilibrium](../../correlated-equilibria/is-correlated-eq.md)
- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Proof depends on

- [Optimistic Hedge achieves polylogarithmic individual regret in general-sum games](optimistic-hedge-polylog-regret.md)
- [No-swap-regret dynamics converge to correlated equilibria](../../no-regret-dynamics/no-swap-regret-dynamics-converge-to-correlated-equilibria.md)
- [Higher-order smoothness of Optimistic Hedge iterates](higher-order-smoothness-optimistic-hedge.md)

## Sources

- I. Anagnostides, C. Daskalakis, G. Farina, M. Fishelson, N. Golowich, T. Sandholm, "Near-Optimal No-Regret Learning for Correlated Equilibria in Multi-Player General-Sum Games", STOC 2022, arXiv:2111.06008, Theorems 1.1 and 1.3 and Corollary 1.2.
