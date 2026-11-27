# Stochastic case

The function is observed through noisy evaluations: an evaluation at a point returns a random reward in $[0, 1]$ whose
mean is the value of the function there. StoSOO extends SOO by evaluating each node several times and comparing upper
confidence bounds, and needs no knowledge of the smoothness. HOO, for a known dissimilarity, plays one point per node
in a tree of coverings and chooses the node to play through optimistic B-values; its expected cumulative regret is
bounded through a near-optimality dimension defined with packing numbers.

- [Noisy evaluations](noisy-evaluations.md)
- [Stochastic simultaneous optimistic optimization (StoSOO)](stosoo.md)
- [Tree of coverings](tree-of-coverings.md)
- [Dissimilarity](dissimilarity.md)
- [Packing number](packing-number.md)
- [Geometrically shrinking regions](geometrically-shrinking-regions.md)
- [Weakly Lipschitz function](weakly-lipschitz-function.md)
- [Near-optimality dimension through packing numbers](near-optimality-dimension-through-packing-numbers.md)
- [Cumulative pseudo-regret](cumulative-pseudo-regret.md)
- [Hierarchical optimistic optimization (HOO)](hoo.md)
- [Regions of small suboptimality](regions-of-small-suboptimality.md)
- [Plays below a suboptimal node by HOO](plays-below-a-suboptimal-node-by-hoo.md)
- [Regret of HOO](regret-of-hoo.md)

## Sources

- M. Valko, A. Carpentier and R. Munos, *Stochastic simultaneous optimistic optimization*, Proceedings of the 30th
  International Conference on Machine Learning (ICML 2013), PMLR 28, <https://proceedings.mlr.press/v28/valko13.html>.
- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Sections 3.4 and 4.2.
