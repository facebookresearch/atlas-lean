# Gradient of the weighted finite-sum objective

Let $n \ge 1$, let $f_i:\mathbb R^d\to\mathbb R$ be differentiable at
$x\in\mathbb R^d$ for every $i=1,\ldots,n$, and fix weights
$v\in\mathbb R^n$. The weighted objective $f_v$ is differentiable at $x$,
with Euclidean gradient

$$
\nabla f_v(x)=\frac{1}{n}\sum_{i=1}^n v_i\nabla f_i(x).
$$

With all weights set to one, this gives the gradient of the original
objective $f$. The weights are held fixed when differentiating.

To see the formula, compute the Fréchet derivative in sup-norm coordinates;
the sup and Euclidean norms are equivalent in finite dimension. By the
finite-sum and constant-scalar derivative rules, it sends a direction $h$ to

$$
\frac{1}{n}\sum_{i=1}^n v_i\langle \nabla f_i(x),h\rangle
= \left\langle\frac{1}{n}\sum_{i=1}^n v_i\nabla f_i(x),h\right\rangle.
$$

The dot-product characterization identifies the Euclidean gradient.

## Depends on

- [Weighted finite-sum objective](weighted-finite-sum-objective.md)

## Proof depends on

- [Fréchet derivative of a constant scalar multiple](../../calculus-in-normed-spaces/frechet-derivatives/derivatives-of-sums-constants-and-scalar-multipl/has-fderiv-at-const-smul.md)
- [Fréchet derivative of a finite sum](../../calculus-in-normed-spaces/frechet-derivatives/derivatives-of-sums-constants-and-scalar-multipl/has-fderiv-at-sum.md)
- [A Fréchet derivative given by a dot product is a gradient](../../real-functions/multivariable-calculus/gradient/has-gradient-at-of-lp.md)

## Sources

- R. M. Gower, N. Loizou, X. Qian, A. Sailanbayev, E. Shulgin, and
  P. Richtárik, [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4),
  arXiv:1901.09401v4, Section 1.2, the differentiation of equation (4)
  used in the first equality of equation (5).
