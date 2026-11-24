# Finite-sample expressivity of two-layer ReLU networks

Let $x_1, \dots, x_n$ be distinct points of a real inner product space $E$ and $y \in \mathbb{R}^n$ arbitrary targets. Then there are $a \in E$ and $b, w \in \mathbb{R}^n$ such that the [two-layer ReLU network](relu-net.md) $c(x) = \sum_j w_j \max(\langle a, x\rangle - b_j, 0)$ satisfies $c(x_i) = y_i$ for every $i$. On $E = \mathbb{R}^d$, with $a \in \mathbb{R}^d$, the network has $2n + d$ weights.

Proof: a vector space over $\mathbb{R}$ is not a finite union of proper subspaces, so some $a$ lies outside each hyperplane $(x_i - x_j)^\perp$, $i \ne j$, and the projections $z_i = \langle a, x_i\rangle$ are distinct. With $b_j = z_j - \delta$ for a margin $\delta > 0$ smaller than every gap $\lvert z_i - z_j\rvert$, sorting the points interleaves thresholds and projections, so the system $c(x_i) = y_i$, linear in $w$, has the matrix of [the interleaved ReLU lemma](det-relu-matrix-ne-zero.md), up to a simultaneous permutation of rows and columns, and is solvable.

The source states the theorem for "a sample of size $n$", a set of points; its proof uses that the points are distinct, and the hypothesis is necessary, since two copies of a point with different labels cannot be fitted. The statement holds in any real inner product space, $\mathbb{R}^d$ included.

Networks of this size can thus fit any labelling of the training sample, random labels included. This is the observation of the source: the effective capacity of such a class is large enough to memorize the data, so a [uniform deviation bound](../../generalization-bounds-and-concentration/README.md) over the whole class cannot explain why networks trained on real labels generalize.

## Background

- [Universal approximation theorem](../../../../Analysis/approximation-theory/universal-approximation.md): background, the classical expressivity result for one-hidden-layer networks, uniform approximation on compact sets as the width grows, where this theorem gives exact interpolation of a finite sample with width $n$.

## Sources

- C. Zhang, S. Bengio, M. Hardt, B. Recht and O. Vinyals, *Understanding deep learning requires rethinking generalization*, ICLR 2017, arXiv:1611.03530, Theorem 1 (proof in Appendix C).
