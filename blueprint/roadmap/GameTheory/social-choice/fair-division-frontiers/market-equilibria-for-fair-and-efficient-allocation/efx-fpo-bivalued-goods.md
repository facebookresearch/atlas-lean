# EFX and fractionally Pareto optimal allocations for bivalued instances

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Assume there are $0 < a < b$ with $v_i(g) \in \{a, b\}$ for all $i, g$. Then an allocation that is simultaneously EFX and fractionally Pareto optimal exists and can be computed in polynomial time.

## Proof sketch

Run a market-based algorithm that keeps an MBB-supported allocation, where by scaling one may take $a = 1$ and $b = k > 1$; prices take only two levels relative to each agent's MBB ratio, which makes price-envy-freeness up to any good (the price analogue of EFX) maintainable through transfers along MBB alternating paths and price rises by the factor $k$. Termination follows from a potential on spending levels; the first welfare theorem gives fPO, and the price-EFX condition together with MBB support gives EFX.

## Depends on

- [Fractional Pareto optimality](fractional-pareto-optimality.md)
- [Envy-freeness up to any good](../../../not-yet-classified/part-01/indivisible/is-efx.md)

## Proof depends on

- [First welfare theorem: price-supported allocations are fractionally Pareto optimal](first-welfare-theorem-mbb-fpo.md)
- [Maximum bang-per-buck allocation supported by prices](maximum-bang-per-buck-allocation.md)

## Sources

- J. Garg, A. Murhekar, "Computing fair and efficient allocations with few utility values", SAGT 2021; Theoretical Computer Science 962 (2023).
