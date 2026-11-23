# Weighted finite-sum objective

Let $n \ge 1$ and let $f_i:\mathbb R^d\to\mathbb R$, $i=1,\ldots,n$, be
differentiable. The source works with smooth components, not necessarily
convex. For a sampling vector $v$ with law $\mathcal D$, the weighted
objective $f_v$ and the original objective $f$ are

$$
f_v(x)=\frac{1}{n}\sum_{i=1}^n v_i f_i(x),
\qquad f(x)=\frac{1}{n}\sum_{i=1}^n f_i(x).
$$

For each draw the weights are held fixed when differentiating. In finite
coordinates the sup norm and Euclidean norm are equivalent, so we can
compute the Fréchet derivative with the sup norm. For a direction $h$,
the rules for finite sums and constant scalar multiples give

$$
D f_v(x)[h]
= \frac{1}{n}\sum_{i=1}^n v_i\langle \nabla f_i(x),h\rangle
= \left\langle\frac{1}{n}\sum_{i=1}^n v_i\nabla f_i(x),h\right\rangle.
$$

The dot-product rule identifies the Euclidean gradient as
$\nabla f_v(x)=n^{-1}\sum_{i=1}^n v_i\nabla f_i(x)$. The same calculation
with all weights set to one gives the formula for $\nabla f(x)$.

For each fixed $x$, the value $f_v(x)$ and each coordinate of
$\nabla f_v(x)$ are integrable, since each is a finite linear combination
of integrable weights with deterministic coefficients. Take the gradient
expectation coordinatewise. Applying linearity of the real integral to
the value and to each gradient coordinate, and using
$\mathbb E_{\mathcal D}[v_i]=1$, gives

$$
\mathbb E_{\mathcal D}[f_v(x)]=f(x),
\qquad \mathbb E_{\mathcal D}[\nabla f_v(x)]=\nabla f(x).
$$

Thus (4) minimizes $x\mapsto\mathbb E_{\mathcal D}[f_v(x)]$ over
$\mathbb R^d$, not the objective for a particular draw. Neither identity
requires a second moment.

## Depends on

- [Sampling vector](sampling-vector.md)
- [Expected value of a random variable](../../../Probability/foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

- [Fréchet derivative of a constant scalar multiple](../../calculus-in-normed-spaces/frechet-derivatives/derivatives-of-sums-constants-and-scalar-multipl/has-fderiv-at-const-smul.md)
- [Fréchet derivative of a finite sum](../../calculus-in-normed-spaces/frechet-derivatives/derivatives-of-sums-constants-and-scalar-multipl/has-fderiv-at-sum.md)
- [A Fréchet derivative given by a dot product is a gradient](../../real-functions/multivariable-calculus/gradient/has-gradient-at-of-lp.md)
- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)

## Sources

- R. M. Gower, N. Loizou, X. Qian, A. Sailanbayev, E. Shulgin, and
  P. Richtárik, [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4),
  arXiv:1901.09401v4, Section 1, equation (1), and Section 1.2, equations (4)–(5).
