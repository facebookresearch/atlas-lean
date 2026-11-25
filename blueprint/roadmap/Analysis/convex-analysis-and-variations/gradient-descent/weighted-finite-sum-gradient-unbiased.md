# Unbiasedness of the weighted finite-sum gradient

Let $n \ge 1$, let $f_i:\mathbb R^d\to\mathbb R$ be differentiable at
$x\in\mathbb R^d$ for every $i=1,\ldots,n$, and let $v$ be a sampling
vector of law $\mathcal D$ on $\mathbb R^n$. At this fixed $x$ every
coordinate of the Euclidean gradient $\nabla f_v(x)$ is integrable, and

$$
\mathbb E_{\mathcal D}[\nabla f_v(x)]=\nabla f(x),
$$

where the vector on the left is the collection of the real expectations of
its coordinates.

By the weighted gradient formula, coordinate $j$ of $\nabla f_v(x)$ is a
finite sum of the integrable weights $v_i$ multiplied by the deterministic
coefficients $(\nabla f_i(x))_j/n$. Each constant multiple is integrable, so
the finite sum is integrable. Applying additivity and homogeneity of the
real integral to each coordinate gives

$$
\mathbb E_{\mathcal D}[(\nabla f_v(x))_j]
=\frac{1}{n}\sum_{i=1}^n \mathbb E_{\mathcal D}[v_i](\nabla f_i(x))_j
=(\nabla f(x))_j.
$$

The last equality uses the unit coordinate means and the gradient formula
with all weights equal to one. No finite second moments are needed.

## Depends on

- [Sampling vector](sampling-vector.md)
- [Weighted finite-sum objective](weighted-finite-sum-objective.md)
- [Expected value of a random variable](../../../Probability/foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

- [Gradient of the weighted finite-sum objective](weighted-finite-sum-gradient.md)
- [Integrability of a constant left multiple](../../../MeasureTheory/integration/integrability-of-sums-and-constant-multiples/integrable-const-mul.md)
- [Integrability of a finite pointwise sum](../../../MeasureTheory/integration/integrability-of-sums-and-constant-multiples/integrable-finset-sum.md)
- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)

## Sources

- R. M. Gower, N. Loizou, X. Qian, A. Sailanbayev, E. Shulgin, and
  P. Richtárik, [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4),
  arXiv:1901.09401v4, Section 1.2, equation (5), with the weighted
  objective from equation (4).
