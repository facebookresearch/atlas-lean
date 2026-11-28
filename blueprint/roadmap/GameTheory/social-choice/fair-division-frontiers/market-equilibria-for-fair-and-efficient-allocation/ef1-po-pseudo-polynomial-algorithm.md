# EF1 and Pareto optimal allocations in pseudo-polynomial time

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Assume integer valuations $v_i(g) \in \{0, 1, \dots, V\}$. There is an algorithm running in time polynomial in $n$, $\lvert M \rvert$ and $V$ that outputs an allocation which is EF1 and Pareto optimal; for every $\varepsilon > 0$ an $\varepsilon$-EF1 and $\varepsilon$-Pareto optimal allocation can be found in time polynomial in $n$, $\lvert M \rvert$, $1/\varepsilon$ and $\log V$. Moreover, for nonnegative integer (equivalently, by scaling, rational) additive valuations an allocation that is EF1 and fractionally Pareto optimal always exists.

## Proof sketch

Maintain an integral MBB-supported allocation with prices, and perform local transfers along alternating MBB paths from the least spender, raising prices of the least spender's component when no transfer is possible. Prices are kept as powers of $(1+\varepsilon)$ after rounding valuations, which bounds the number of price-rise steps polynomially in $n$, $\lvert M\rvert$ and $V$; at termination the allocation is approximately pEF1 and fPO for the rounded valuations, which for a small enough $\varepsilon$ makes it EF1 and Pareto optimal for the original integer valuations. The existence of EF1 and fPO allocations for integer valuations follows by a limiting argument over such allocations; rational valuations reduce to integer ones by scaling.

## Depends on

- [Fractional Pareto optimality](fractional-pareto-optimality.md)
- [Is EF1](../../../not-yet-classified/part-01/indivisible/is-ef1.md)
- [Pareto-optimal allocation](../../../not-yet-classified/part-01/indivisible/is-pareto-optimal.md)

## Proof depends on

- [MBB-supported price envy-freeness up to one good implies EF1](mbb-pef1-implies-ef1.md)
- [Price envy-freeness up to one good](price-envy-freeness-up-to-one-good.md)
- [Maximum bang-per-buck allocation supported by prices](maximum-bang-per-buck-allocation.md)
- [First welfare theorem: price-supported allocations are fractionally Pareto optimal](first-welfare-theorem-mbb-fpo.md)

## Sources

- S. Barman, S. K. Krishnamurthy, R. Vaish, "Finding Fair and Efficient Allocations", EC 2018, arXiv:1707.04731, Section 2.1 and Theorem 2.
