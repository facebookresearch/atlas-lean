# Weighted finite-sum objective

Let $n \ge 1$ and let $f_i:\mathbb R^d\to\mathbb R$, $i=1,\ldots,n$, be
differentiable. The source works with smooth components, not necessarily
convex. For a sampling vector $v$ with law $\mathcal D$, the weighted
objective $f_v$ and the original objective $f$ are

$$
f_v(x)=\frac{1}{n}\sum_{i=1}^n v_i f_i(x),
\qquad f(x)=\frac{1}{n}\sum_{i=1}^n f_i(x).
$$

For each draw the weights are held fixed when differentiating, so
$\nabla f_v(x)=n^{-1}\sum_{i=1}^n v_i\nabla f_i(x)$. For each fixed $x$,
$f_v(x)$ and the vector $\nabla f_v(x)$ are integrable: each is a finite
linear combination of integrable weights with deterministic coefficients.
By linearity and $\mathbb E_{\mathcal D}[v_i]=1$,

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

- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)

## Sources

- R. M. Gower, N. Loizou, X. Qian, A. Sailanbayev, E. Shulgin, and
  P. Richtárik, [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4),
  arXiv:1901.09401v4, Section 1, equation (1), and Section 1.2, equations (4)–(5).
