# Uncoupled dynamics with logarithmic swap regret

There are uncoupled learning dynamics for finite $m$-player normal-form games in which, when all players adopt them, every player's swap regret after $T$ rounds is $O\bigl(\mathrm{poly}(m, n) \cdot \log T\bigr)$, with a time-invariant learning rate, while each player's swap regret against adversarial utilities stays $O(\sqrt T)$. The dynamics use the Blum–Mansour construction with external-regret learners given by optimistic follow-the-regularized-leader with a logarithmic barrier regularizer, and the average correlated distribution of play is an $O(\log T / T)$-approximate correlated equilibrium.

## Proof sketch

The log-barrier regularizer makes the iterates multiplicatively stable, which yields an RVU-type bound in local norms with a variation term controllable by the other players' stability. A self-concordance argument shows that the sum over players of the second-order path lengths is $O(\log T)$; combining with the RVU property gives logarithmic swap regret for each player without needing higher-order smoothness.

## Depends on

- [Internal and swap regret minimization via stationary distributions](swap-regret-stationary-distribution-dynamics.md)

## Proof depends on

- [Regret bounded by variation in utilities for optimistic algorithms](rvu-property-optimistic-algorithms.md)

## Sources

- I. Anagnostides, G. Farina, C. Kroer, C.-W. Lee, H. Luo, T. Sandholm, "Uncoupled Learning Dynamics with O(log T) Swap Regret in Multiplayer Games", NeurIPS 2022, arXiv:2204.11417.
