# Optimal realizable sample complexity of the hard-margin support vector machine

For affine halfspaces $\{x : \langle w, x\rangle + b \ge 0\}$ in $\mathbb{R}^n$, $n \ge 1$, in the realizable setting, the hard-margin support vector machine (which outputs the maximum-margin separator of the sample) is a PAC learner with sample complexity

$$
\Theta\!\left(\frac{n}{\varepsilon} + \frac{1}{\varepsilon}\log\frac{1}{\delta}\right).
$$

This resolves a question of Vapnik and Chervonenkis (1974) and gives the first proper and computationally efficient learner of halfspaces attaining the optimal PAC rate.

## Proof sketch

The support vector machine is a stable compression scheme: its output is determined by at most $n+1$ support vectors and does not change when non-support examples are removed. Stable compression schemes of size $k$ have, from $m > 2k$ examples, risk below $\tfrac{2}{m-2k}(k\ln 4 + \ln(1/\delta))$ with probability at least $1-\delta$; with $k = n+1$ this gives the upper bound without the extra logarithmic factor. The matching lower bound is the standard PAC lower bound for the VC dimension $n+1$ of affine halfspaces in $\mathbb{R}^n$.

## Depends on

- [Hard-margin SVM and margin-based sample complexity](../../../../supervised-learning/logistic-regression-and-support-vector-machines/hard-margin-svm-and-margin-based-sample-complexity.md)

## Proof depends on

- [Stable compression schemes are optimal PAC learners](stable-compression-optimal-pac-bound.md)
- [Shattering lower bound for PAC learning](../../../../generalization-bounds-and-concentration/shattering-lower-bound-for-pac-learning.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818, Theorem 12 and Section 5.
