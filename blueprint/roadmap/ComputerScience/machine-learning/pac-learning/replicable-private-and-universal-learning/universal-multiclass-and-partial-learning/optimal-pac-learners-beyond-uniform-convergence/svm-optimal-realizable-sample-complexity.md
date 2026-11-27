# Optimal realizable sample complexity of the hard-margin support vector machine

For homogeneous halfspaces in $\mathbb{R}^n$ in the realizable setting, the hard-margin support vector machine (which outputs the maximum-margin separator of the sample) is a PAC learner with sample complexity

$$
\Theta\!\left(\frac{n}{\varepsilon} + \frac{1}{\varepsilon}\log\frac{1}{\delta}\right).
$$

This resolves a question of Vapnik and Chervonenkis (1974) and gives the first proper and computationally efficient learner of halfspaces attaining the optimal PAC rate.

## Proof sketch

The support vector machine is a stable compression scheme: its output is determined by at most $n$ support vectors and does not change when non-support examples are removed. Stable compression schemes of size $k$ satisfy a leave-one-out bound of order $k/n$ uniformly over samples, and a refined argument exploiting that removing a non-support vector leaves the output unchanged gives the high-probability bound without the extra logarithmic factor. The matching lower bound is the standard PAC lower bound for VC dimension $n$.

## Depends on

- [Hard-margin SVM and margin-based sample complexity](../../../../supervised-learning/logistic-regression-and-support-vector-machines/hard-margin-svm-and-margin-based-sample-complexity.md)

## Proof depends on

- [Proper learners attain the optimal PAC rate exactly when the dual Helly number is bounded](proper-learning-dual-helly-characterization.md)
- [Generalization bound for sample compression schemes](../../../../generalization-bounds-and-concentration/generalization-bound-for-sample-compression-schemes.md)
- [Leave-one-out bounds give optimal high-probability risk bounds for aggregated learners](leave-one-out-to-high-probability.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818.
