# Pure deviations suffice to check a mixed Nash equilibrium

In a finite game, the expected payoff is affine in each player's own mixed strategy: for every player $i$, every mixed profile $\sigma$ and every mixed strategy $\tau$ of $i$, $U_i(\tau, \sigma_{-i}) = \sum_{a \in S_i} \tau(a)\,U_i(a, \sigma_{-i})$, where $a$ also denotes the point mass at $a$; hence $U_i$ is multilinear in $(\sigma_j)_j$. Consequently $\sigma$ is a mixed Nash equilibrium if and only if $U_i(a, \sigma_{-i}) \le U_i(\sigma)$ for every player $i$ and every pure strategy $a \in S_i$.

Proof. Grouping the terms of the expected-payoff sum by the strategy of player $i$ gives the displayed identity. If no pure deviation is profitable, then $U_i(\tau, \sigma_{-i}) = \sum_a \tau(a)U_i(a, \sigma_{-i}) \le U_i(\sigma)$ because the weights $\tau(a)$ are nonnegative and sum to $1$; conversely, a point mass is a mixed strategy.

## Depends on

- [Expected payoff of a mixed profile](expected-payoff.md): expected payoff of a mixed profile.
- [Mixed Nash equilibrium](is-mixed-nash.md): mixed Nash equilibrium.

## Sources

- N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, Section 2.1.1, Theorem 2.1 and discussion, <https://www.cs.cmu.edu/~sandholm/cs15-892F13/algorithmic-game-theory.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
