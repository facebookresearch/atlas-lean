# Maximin share approximation beyond three quarters

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every instance a complete $\bigl(\tfrac34 + \tfrac{3}{3836}\bigr)$-MMS allocation exists. The earlier guarantees $\tfrac34 + O(\tfrac1n)$ came from the Garg–Taki algorithm (reduction rules followed by bag filling from bags $\{g_k, g_{2n+1-k}\}$), and a known tight example shows that this algorithm cannot guarantee $\tfrac34 + \Omega(1)$.

## Proof sketch

Fix $\varepsilon > 0$ and apply the reduction rules for the factor $\tfrac34 + \varepsilon$. Unlike for factor $\tfrac34$, these rules may lower the maximin shares of the remaining agents; the proof shows they lose at most a factor $1 - 4\varepsilon$ over any number of applications, and then orders and normalizes the reduced instance. Agents are split according to whether the good $g_{2n+1}$ is small for them. If few agents are problematic, a modified bag-filling algorithm works; otherwise a new reduction rule gives the two most valuable goods to one agent, and bags are initialized with three goods $\{g_k, g_{2n-k+1}, g_{2n+k}\}$ before bag filling. Balancing the two cases gives the constant $3/3836$.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Proof depends on

- [Valid reduction rules preserving maximin shares of the remaining agents](valid-reductions-maximin-share.md)
- [Three-quarters maximin share allocations in polynomial time](three-quarters-mms-polynomial-time.md)

## Sources

- H. Akrami, J. Garg, "Breaking the 3/4 Barrier for Approximate Maximin Share", SODA 2024, arXiv:2307.07304.
