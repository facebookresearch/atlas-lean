# Moulin's mechanism is group-strategyproof and budget-balanced

For every cross-monotonic cost-sharing scheme $\xi$, Moulin's mechanism is group-strategyproof: no coalition of agents can misreport so that every member is weakly better off and some member strictly better off. It satisfies voluntary participation and consumer sovereignty, is $\gamma$-budget-balanced whenever $\xi$ is, and makes no positive transfers when shares are nonnegative.

## Proof sketch

Suppose a coalition misreports and its members weakly gain. Members who are served after misreporting pay at most their utility. Cross-monotonicity shows the truthful largest willing coalition is contained in the new one restricted appropriately, so shares can only weakly increase for truthfully served members, contradicting a strict gain.

## Depends on

- [Moulin's iterative-pruning mechanism](moulins-iterative-pruning-mechanism.md)
- [Dominant-strategy incentive compatibility](../../mechanism-design/revelation-principle/is-dominant-strategy-incentive-compatibl.md)

## Proof depends on

- [Moulin pruning reaches the unique largest willing coalition](moulin-pruning-reaches-the-unique-largest-willing-coalition.md)

## Sources

- Kamal Jain and Mohammad Mahdian, "Cost Sharing", Algorithmic Game Theory, Cambridge University Press, 2007.
- Herve Moulin and Scott Shenker, "Strategyproof Sharing of Submodular Costs: Budget Balance versus Efficiency", Economic Theory, 2001.
