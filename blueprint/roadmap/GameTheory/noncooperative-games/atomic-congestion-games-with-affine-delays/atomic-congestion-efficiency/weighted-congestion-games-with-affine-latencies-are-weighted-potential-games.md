# Weighted congestion games with affine latencies are weighted potential games

In a weighted atomic congestion game with affine latencies $\ell_e(x) = a_e x + b_e$, the function $\Phi(s) = \frac12 \sum_e \bigl(a_e L_e(s)^2 + a_e \sum_{i : e \in R_i(s_i)} w_i^2\bigr) + \sum_e b_e L_e(s)$ changes by exactly the deviator's cost change under unilateral deviations; hence these games have the finite improvement property and pure Nash equilibria. With equal weights the game has the finite improvement property for arbitrary latencies, while with general weights and nonlinear latencies pure equilibria need not exist.

## Proof sketch

Expand the change in $\Phi$ when player $i$ moves from $R_i(a)$ to $R_i(b)$: on each affected resource the quadratic terms produce exactly $w_i \ell_e$ evaluated at the new load minus the old, matching the cost change.

## Depends on

- [Weighted atomic congestion game](weighted-atomic-congestion-game.md)
- [Exact potential](../../potential-games/is-exact-potential.md)

## Proof depends on

- [Generalized ordinal potentials give the finite improvement property](../../potential-games/potential-game-characterizations/generalized-ordinal-potentials-give-the-finite-improvement-property.md)

## Sources

- Noam Nisan, Tim Roughgarden, Eva Tardos and Vijay V. Vazirani, "Algorithmic Game Theory", Cambridge University Press, 2007.
