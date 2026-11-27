# Multicast cost is monotone and submodular

The multicast cost function $c(R)$ is nonnegative, monotone, and submodular in $R$; its Shapley value splits the cost of each link equally among the receivers in the set below that link.

## Proof sketch

The cost is a sum over links of $c_e$ times the indicator that some receiver lies below $e$, each a monotone submodular OR-function; the Shapley value of an OR-game splits its cost equally among the relevant agents.

## Depends on

- [Multicast cost-sharing problem](multicast-cost-sharing-problem.md)
- [Submodular cost-sharing game](../cross-monotonic-cost-sharing/submodular-cost-sharing-game.md)

## Proof depends on

- [Subset-weight and random-order formulas for the Shapley value agree](../cross-monotonic-cost-sharing/subset-weight-and-random-order-formulas-for-the-shapley-value-agree.md)

## Sources

- Herve Moulin and Scott Shenker, "Strategyproof Sharing of Submodular Costs: Budget Balance versus Efficiency", Economic Theory, 2001.
- Joan Feigenbaum, Christos H. Papadimitriou and Scott Shenker, "Sharing the Cost of Multicast Transmissions", Journal of Computer and System Sciences, 2001.
- Joan Feigenbaum, Michael Schapira and Scott Shenker, "Distributed Algorithmic Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
