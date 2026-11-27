# Mechanism design

Mechanism design studies how to choose the rules of a game, with or without money, so that self-interested agents with private information reach a desired outcome in equilibrium: the revelation principle, incentive compatibility and Myerson's characterization of single-parameter mechanisms, revenue equivalence and optimal auctions, Vickrey–Clarke–Groves mechanisms, and impossibility results for bilateral trade.

The [revelation principle](revelation-principle/README.md) reduces the design problem to direct mechanisms in which truthful reporting is an equilibrium, in dominant strategies or in the Bayesian sense. With quasi-linear utilities and one-dimensional private values, [Myerson's lemma](myerson-s-lemma-and-revenue-equivalence/README.md) characterizes incentive compatibility: the allocation must be monotone, and the payments are then determined by the envelope formula up to the utility of the lowest type, which gives revenue equivalence. Integrating the payment formula against the value distribution expresses expected revenue as expected *virtual surplus*, which reduces [optimal auction design](optimal-auctions-and-virtual-valuations/README.md) to maximizing virtual valuations pointwise; for one bidder whose virtual valuation changes sign once, a posted price at the sign change is optimal. For welfare rather than revenue, [Vickrey–Clarke–Groves mechanisms](vickrey-clarke-groves-mechanisms/README.md) make truthful reporting a dominant strategy in every quasi-linear environment, and the [Myerson–Satterthwaite theorem](myerson-satterthwaite.md) shows that no Bayesian incentive-compatible, individually rational mechanism trades efficiently between a buyer and a seller with overlapping value ranges.

- [Revelation principle](revelation-principle/README.md)
- [Myerson's lemma and revenue equivalence](myerson-s-lemma-and-revenue-equivalence/README.md)
- [Optimal auctions and virtual valuations](optimal-auctions-and-virtual-valuations/README.md)
- [Vickrey–Clarke–Groves mechanisms](vickrey-clarke-groves-mechanisms/README.md)
- [Myerson–Satterthwaite theorem](myerson-satterthwaite.md)
- [Bilateral trade](bilateral-trade/README.md)
- [Screening with two types](screening-with-two-types/README.md)
- [Bilateral trade impossibility (dominant-strategy form)](bilateral-trade-impossibility.md)
- [Characterization of proper scoring rules](characterization-of-proper-scoring-rules.md)
- [Scoring rules and properness for finite outcomes](remaining-clauses-of-scoring-rules-and-properness.md)
- [Combinatorial Agency and Rational Cryptography](contracts-and-rational-cryptography/README.md)
- [Reputation Systems and Peer-to-Peer Incentives](reputation-and-peer-to-peer-incentives/README.md)
- [Characterizations of Dominant-Strategy Incentive Compatibility](dsic-characterizations/README.md)
- [Combinatorial Auctions](combinatorial-auctions/README.md)
- [Divisible Resource Allocation Mechanisms](divisible-resource-allocation/README.md)
- [Facility Location without Money](facility-location-without-money/README.md)
- [Indirect Mechanisms and Ex-Post Implementation](indirect-mechanisms-and-ex-post-implementation/README.md)
- [Ironing and Optimal Auctions for Irregular Distributions](ironing-and-irregular-distributions/README.md)
- [Online Mechanism Design](online-mechanism-design/README.md)
- [Prior-Free Digital Goods and Position Auctions](prior-free-and-position-auctions/README.md)
- [Single-Parameter Auctions](single-parameter-auctions/README.md)
- [Standard Proper Scoring Rules](standard-scoring-rules/README.md)
- [Truthful Scheduling and Budget-Constrained Auctions](truthful-scheduling-and-budgets/README.md)

## Related topics

- [Noncooperative games](../noncooperative-games/README.md): Nash equilibrium and its existence ([Nash's theorem](../noncooperative-games/nash-s-theorem/README.md)), the solution concept that mechanisms are designed to induce.
- [Selfish routing and the price of anarchy](../noncooperative-games/selfish-routing-and-the-price-of-anarchy/README.md): how inefficient the equilibria of a given game can be, the question mechanism design answers by changing the game.
- [Correlated equilibria](../noncooperative-games/correlated-equilibria/README.md): equilibria with a mediator who sends private recommendations, the communication counterpart of direct mechanisms.
- [Social choice theory](../social-choice/README.md): aggregation of preferences without money, where the Gibbard–Satterthwaite theorem rules out nontrivial strategy-proof rules.
- [Matching markets](../matching-markets/README.md): mechanisms without money for two-sided matching with ordinal preferences and private outcomes, where Roth's impossibility theorem rules out stable mechanisms that are strategy-proof for both sides.

## Research directions

- [Menu-size complexity of revenue approximation](menu-size-complexity-of-revenue-approximation.md)
- [Optimal prophet-secretary ratio](optimal-prophet-secretary-ratio.md)
