# Lasry–Lions uniqueness of mean field equilibria

Suppose the cost satisfies the Lasry–Lions monotonicity condition

$$\sum_y (F(y, m_1) - F(y, m_2))(m_1(y) - m_2(y)) > 0 \quad \text{for probability vectors } m_1 \ne m_2 .$$

Then there is at most one [mean field equilibrium](is-mean-field-equilibrium.md).

If $m_1$ and $m_2$ are equilibria, $\int F(\cdot, m_1)\, d(m_1 - m_2) \le 0$ and
$\int F(\cdot, m_2)\, d(m_2 - m_1) \le 0$; adding them gives
$\int (F(\cdot, m_1) - F(\cdot, m_2))\, d(m_1 - m_2) \le 0$, so $m_1 = m_2$. The condition expresses
crowd aversion: a cost that increases with the mass at the chosen state, such as $F(y, m) = m(y)$,
satisfies it. The same two-line argument proves uniqueness for the mean field game system, after the
[Lasry–Lions identity](lasry-lions-identity.md) is used to dispose of the Hamiltonian terms.

## Background

- [Wardrop equilibria have unique edge latencies](../selfish-routing-and-the-price-of-anarchy/latency-edge-flow-eq.md):
  the same monotonicity argument for routing games (Beckmann, McGuire and Winsten), where
  nondecreasing latencies give uniqueness of latencies rather than of flows.

## Sources

- J.-M. Lasry and P.-L. Lions, "Mean field games", Japan. J. Math. 2 (2007), 229–260.
- P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*, version of 27 September 2013, Proposition 2.9 and condition (7).
