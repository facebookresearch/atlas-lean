# The marginal-cost multicast mechanism is efficient and strategyproof

The marginal-cost mechanism serves the largest welfare-maximizing receiver set $R^*$ and charges each receiver $j$ its VCG payment, its value minus its marginal contribution to maximum net welfare. It maximizes net welfare, is strategyproof, makes no positive transfers and satisfies voluntary participation; net welfare is supermodular, so the welfare-maximizing sets are closed under union and a unique largest one exists and is computable by a bottom-up pass over the tree. It is not budget-balanced in general.

## Proof sketch

Net welfare decomposes over the tree; at each node keep the subtree iff its welfare is nonnegative. Truthfulness and the payment properties are those of VCG with Clarke pivots.

## Depends on

- [Multicast cost-sharing problem](multicast-cost-sharing-problem.md)
- [Vickrey–Clarke–Groves theorem](../../mechanism-design/vickrey-clarke-groves-mechanisms/is-incentive-compatible-groves.md)

## Proof depends on

- [VCG with Clarke pivot payments is incentive compatible](../../mechanism-design/vickrey-clarke-groves-mechanisms/is-incentive-compatible-clarke.md)

## Sources

- Herve Moulin and Scott Shenker, "Strategyproof Sharing of Submodular Costs: Budget Balance versus Efficiency", Economic Theory, 2001.
- Joan Feigenbaum, Christos H. Papadimitriou and Scott Shenker, "Sharing the Cost of Multicast Transmissions", Journal of Computer and System Sciences, 2001.
- Joan Feigenbaum, Michael Schapira and Scott Shenker, "Distributed Algorithmic Mechanism Design", Algorithmic Game Theory, Cambridge University Press, 2007.
