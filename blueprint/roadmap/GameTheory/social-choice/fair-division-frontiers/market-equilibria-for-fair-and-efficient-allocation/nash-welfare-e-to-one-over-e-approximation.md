# A 1.45-approximation to maximum Nash welfare from approximately price-EF1 market outcomes

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. There is a polynomial-time algorithm that is a $1.45$-approximation for maximum Nash social welfare with additive valuations; the factor comes from the bound $e^{1/e} \approx 1.4447$ plus an arbitrarily small loss from rounding.

## Proof sketch

Compute an allocation that is MBB-supported and approximately pEF1 with respect to rounded valuations. A key lemma: for identical additive valuations, every $\varepsilon$-EF1 allocation is a $1.45$-approximation of the maximum Nash welfare; prices play the role of the identical valuation. Using the prices, the optimal Nash welfare is bounded above by a product of the agents' MBB ratios times prices of an optimal fractional market allocation; the pEF1 condition limits how much any agent's spending deviates from this benchmark, and optimizing the worst case of $\prod_i (1 + t_i)$ under the resulting constraints yields the factor $e^{1/e}$.

## Depends on

- [Approximation ratio for the Nash social welfare objective](../nash-welfare-fairness-guarantees/nash-social-welfare-approximation-ratio.md)

## Proof depends on

- [MBB-supported price envy-freeness up to one good implies EF1](mbb-pef1-implies-ef1.md)
- [Price envy-freeness up to one good](price-envy-freeness-up-to-one-good.md)
- [Maximum bang-per-buck allocation supported by prices](maximum-bang-per-buck-allocation.md)

## Sources

- S. Barman, S. K. Krishnamurthy, R. Vaish, "Finding Fair and Efficient Allocations", EC 2018, arXiv:1707.04731.
