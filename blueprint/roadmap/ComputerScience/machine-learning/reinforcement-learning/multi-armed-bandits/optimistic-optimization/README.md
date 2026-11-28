# Optimistic optimization

Optimization of a function $f \colon \mathcal X \to \mathbb{R}$ from its values at points chosen one after another,
with a hierarchical partition of $\mathcal X$ given to the algorithm. Following the optimistic principle, the algorithms
expand the cells that may contain a maximizer, given the values seen so far and an assumption on the smoothness of $f$
around a maximizer, and they return a point whose loss is bounded through the near-optimality dimension, a measure of
the quantity of near-optimal points. The pages below set up the partitions, the assumptions and the dimension; the
algorithms are in the subfolder [Deterministic case](deterministic/README.md).

- [Hierarchical partition](hierarchical-partition.md)
- [Exploration trees](exploration-trees.md)
- [Semi-metric](semi-metric.md)
- [Local smoothness around a maximizer](local-smoothness-around-a-maximizer.md)
- [Bounded diameters of the cells](bounded-diameters.md)
- [Well-shaped cells](well-shaped-cells.md)
- [Near-optimality dimension](near-optimality-dimension.md)
- [Loss of a returned point](loss.md)
- [Number of near-optimal cells at a given depth](number-of-near-optimal-cells.md)
- [Deterministic case](deterministic/README.md)

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011).
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Chapters 3 and 4.
