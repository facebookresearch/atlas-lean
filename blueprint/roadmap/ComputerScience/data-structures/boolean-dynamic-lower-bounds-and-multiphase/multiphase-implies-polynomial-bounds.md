# The multiphase conjecture implies polynomial dynamic lower bounds

If the multiphase conjecture holds, then there is a constant $\varepsilon > 0$ such that dynamic reachability in directed graphs, dynamic shortest paths, dynamic subgraph connectivity and several other dynamic graph problems on $n$ vertices require $\max\{t_u, t_q\} \ge n^{\varepsilon}$ for structures with polynomial preprocessing. Moreover, the multiphase conjecture follows from the hypothesis that 3SUM has no $O(n^{2 - \varepsilon})$ algorithm, via a reduction of 3SUM to the multiphase problem using linear hashing.

## Proof sketch

Encode $x_1, \dots, x_k$ in Phase I as $k$ gadgets of a graph, insert the edges encoding $y$ in Phase II, and in Phase III ask a reachability or connectivity query whose answer is the intersection bit of $x_i$ and $y$; the polynomial relation between $k$ and $n$ converts a dynamic algorithm with $n^{o(1)}$ costs into a multiphase solution with $\tau = n^{o(1)}$. For 3SUM, hash the numbers into buckets so that each candidate triple becomes an intersection query between a bucket set and a shifted set.

## Depends on

- [Multiphase conjecture](multiphase-conjecture.md)
- [Dynamic graph problems](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)

## Proof depends on

- [Multiphase conjecture](multiphase-conjecture.md)
- [Dynamic graph problems](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/dynamic-graph-problems.md)

## Sources

- Mihai Pătraşcu, "Towards Polynomial Lower Bounds for Dynamic Problems", STOC (2010).
