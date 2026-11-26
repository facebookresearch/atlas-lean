# Vickrey–Clarke–Groves mechanisms

Agents with quasi-linear utilities report valuations over a set of alternatives. A VCG mechanism chooses an alternative that maximizes the reported social welfare and charges each agent a term independent of its own report minus the reported welfare of the others; each agent's utility is then the social welfare minus a term it cannot influence, so truthful reporting is a dominant strategy (Nisan 2007, Theorem 9.17, crediting Vickrey 1961, Clarke 1971 and Groves 1973). With the Clarke pivot term, the best welfare the others could get without the agent, no agent is ever paid and, for nonnegative valuations, every truthful agent gets a nonnegative utility (Nisan 2007, Lemma 9.20). Vickrey's second-price auction, in which the highest bidder wins and pays the highest competing bid, is the VCG mechanism with Clarke pivot payments for one item, with the possible winners as alternatives (Nisan 2007, §9.3.5.1); it is therefore truthful (Nisan 2007, Proposition 9.13).

- [Social welfare](welfare.md)
- [Welfare of the others](others-welfare.md)
- [Welfare decomposition](welfare-eq.md)
- [The others' welfare ignores the own valuation](others-welfare-update.md)
- [Incentive compatibility (quasi-linear, dominant strategies)](is-incentive-compatible.md)
- [Groves payment](groves-payment.md)
- [Pivot terms independent of the own report](independent-of-own.md)
- [VCG truthfulness, pointwise](groves-payment-truthful.md)
- [Vickrey–Clarke–Groves theorem](is-incentive-compatible-groves.md)
- [Clarke pivot term](clarke-pivot.md)
- [The Clarke pivot term ignores the own report](clarke-pivot-independent.md)
- [VCG with Clarke pivot payments is incentive compatible](is-incentive-compatible-clarke.md)
- [No positive transfers](clarke-payment-nonneg.md)
- [Individual rationality](clarke-utility-nonneg.md)

## Vickrey's second-price auction

- [Single-item valuations](single-item.md)
- [Welfare of a winner](welfare-single-item.md)
- [Others' welfare of a winner](others-welfare-single-item.md)
- [Changing one bid changes one valuation](update-single-item.md)
- [Some other agent exists](nonempty-others.md)
- [Second-price payment](second-price-payment.md)
- [The second-price auction is the VCG mechanism with Clarke pivot payments](groves-payment-single-item.md)
- [Vickrey's theorem](second-price-truthful.md)

## Vickrey–Clarke–Groves mechanisms

- [Efficiency and truthfulness do not imply budget balance](vcg-is-not-budget-balanced.md)

## Second-price auction with least-index tie-break

- [Winner of a second-price auction with least-index tie-break](vickrey-winner.md)
- [Price in a second-price auction](vickrey-price.md)
- [Utility in a second-price auction](vickrey-utility.md)
- [Truthful bidding is weakly dominant in a second-price auction](vickrey-truthful-dominant.md)
- [Truthful bidding in a second-price auction is individually rational](vickrey-ir.md)

## Related topics

- [Revelation principle](../revelation-principle/README.md): dominant-strategy incentive compatibility of direct mechanisms.
- [Myerson–Satterthwaite theorem](../myerson-satterthwaite.md): in bilateral trade no Bayesian incentive-compatible, individually rational mechanism is efficient without a subsidy, so efficiency, budget balance and participation cannot all be had.
- [Gibbard–Satterthwaite theorem](../../social-choice/gibbard-satterthwaite-theorem/README.md): the impossibility without money that quasi-linear transfers circumvent.
- [Selfish routing and the price of anarchy](../../noncooperative-games/selfish-routing-and-the-price-of-anarchy/README.md): the cost of equilibria of a given game, where mechanism design chooses the game.
