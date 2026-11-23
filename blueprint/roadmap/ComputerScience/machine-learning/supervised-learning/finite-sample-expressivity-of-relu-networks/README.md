# Finite-sample expressivity of ReLU networks

A network with one hidden layer of $n$ ReLU units, $c(x) = \sum_{j=1}^n w_j \max(\langle a, x\rangle - b_j, 0)$, has $2n + d$ weights on inputs in $\mathbb{R}^d$ and can take any prescribed values on any $n$ distinct points (Zhang, Bengio, Hardt, Recht and Vinyals 2017, Theorem 1). The proof projects the points on a direction $a$ that separates them, interleaves the thresholds $b_j$ with the projections, and solves a linear system whose matrix $[\max(x_i - b_j, 0)]$ is lower triangular with a positive diagonal. Distinctness of the sample points is necessary: two copies of a point with different labels cannot be fitted.

- [Two-layer ReLU network](relu-net.md)
- [The interleaved ReLU matrix has full rank](det-relu-matrix-ne-zero.md)
- [Finite-sample expressivity of two-layer ReLU networks](exists-relu-net-eq.md)

## Related topics

- [Generalization bounds and concentration](../../generalization-bounds-and-concentration/README.md): uniform deviation bounds over a class, which become vacuous for a class that can fit every labelling of the sample.
- [Backpropagation](../backpropagation/README.md): the gradient computation used to train such networks.
