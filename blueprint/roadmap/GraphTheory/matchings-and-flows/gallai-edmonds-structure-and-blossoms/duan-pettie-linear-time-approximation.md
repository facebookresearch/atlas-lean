# Duan-Pettie linear-time approximation for maximum weight matching in general graphs

There is a deterministic algorithm that, for every $\varepsilon \in (0, 1)$ and every finite graph with $n$ vertices, $m$ edges and nonnegative real edge weights, computes a $(1 - \varepsilon)$-approximate maximum weight matching in

$$
O\!\left(m \, \varepsilon^{-1} \log \varepsilon^{-1}\right)
$$

time in a model with unit-cost comparisons and additions of weights. For each fixed $\varepsilon$ this is linear time, bypassing the $\widetilde{O}(m \sqrt{n})$ running time of the classical exact combinatorial algorithms for maximum cardinality and maximum weight matching.

## Proof sketch

The algorithm is a scaling primal-dual method for Edmonds' linear program with odd-set constraints: it maintains a matching, a laminar family of blossoms and duals $y_v, z_B$ that satisfy relaxed complementary slackness with a slack proportional to the current scale. Over $O(\log \varepsilon^{-1})$ scales of geometrically decreasing granularity it runs Edmonds-type searches that may be truncated, with blossom bookkeeping arranged so that the total work is $O(m \varepsilon^{-1} \log \varepsilon^{-1})$. At the end, the relaxed conditions together with weak duality for the matching polytope bound the loss by an $\varepsilon$ fraction of the optimum.

## Depends on

- [Approximate maximum weight matchings in general graphs](approximate-maximum-weight-matching.md)

## Proof depends on

- [Edmonds' perfect matching polytope theorem](../matching-polytope/perfect-matching-polytope-eq.md)
- [Edmonds' blossom shrinking lemma](edmonds-blossom-shrinking-lemma.md)
- [Correctness and running time of Edmonds' cardinality blossom algorithm](edmonds-cardinality-blossom-algorithm.md)
- [Alternating forests, flowers and blossoms of a matching](alternating-forests-and-blossoms.md)
- [Matching polytope](../matching-polytope/matching-polytope.md)

## Sources

- R. Duan, S. Pettie, "Linear-Time Approximation for Maximum Weight Matching", Journal of the ACM 61 (2014).
- R. Duan, S. Pettie, H.-H. Su, "Scaling Algorithms for Weighted Matching in General Graphs", ACM Transactions on Algorithms 14 (2018), SODA (2017), arXiv:1411.1919.
