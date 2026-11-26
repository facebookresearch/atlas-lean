# EF1 and Pareto optimal allocations in pseudo-polynomial time

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. Assume integer valuations $v_i(g) \in \{0, 1, \dots, V\}$. There is an algorithm running in time polynomial in $n$, $\lvert M \rvert$ and $V$ that outputs an allocation which is EF1 and Pareto optimal. If valuations are positive, the output is moreover fractionally Pareto optimal.

## Proof sketch

Maintain an integral MBB-supported allocation with prices, and perform local transfers along alternating MBB paths from the least spender, raising prices of the least spender's component when no transfer is possible. Prices are kept as powers of $(1+\varepsilon)$ after rounding valuations, which bounds the number of price-rise steps polynomially in $n$, $\lvert M\rvert$ and $V$; at termination the allocation is pEF1, hence EF1 and fPO.

## Depends on

- [Price envy-freeness up to one good](price-envy-freeness-up-to-one-good.md)
- [Fractional Pareto optimality](fractional-pareto-optimality.md)

## Proof depends on

- [MBB-supported price envy-freeness up to one good implies EF1](mbb-pef1-implies-ef1.md)

## Sources

- S. Barman, S. K. Krishnamurthy, R. Vaish, "Finding Fair and Efficient Allocations", EC 2018, arXiv:1707.04731.
