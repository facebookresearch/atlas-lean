# Annealing step is a Metropolis-Hastings step

On a finite nonempty state space, let the proposal $R$ be symmetric, $R(x, y) = R(y, x)$, and let $T > 0$. The annealing step at temperature $T$, which proposes $y$ from $R(x, \cdot)$ and accepts with probability $\min\bigl(1, e^{-\max(V(y) - V(x), 0)/T}\bigr)$, equals the Metropolis-Hastings step with proposal $R$ targeting the Gibbs law $\propto e^{-V/T}$.
