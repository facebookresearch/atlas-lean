# Unbiasedness of the weighted finite-sum value

Let $n \ge 1$, let $f_i:\mathbb R^d\to\mathbb R$ for $i=1,\ldots,n$, and
let $v$ be a sampling vector of law $\mathcal D$ on $\mathbb R^n$. For every
fixed $x\in\mathbb R^d$, the weighted value $f_v(x)$ is integrable and its
real expectation is the original objective value:

$$
\mathbb E_{\mathcal D}[f_v(x)] = f(x).
$$

For fixed $x$, the coefficients $f_i(x)/n$ are deterministic. Multiplying
each integrable coordinate $v_i$ by its coefficient and summing the finitely
many terms shows that $f_v(x)$ is integrable. Taking the real integral term
by term and using $\mathbb E_{\mathcal D}[v_i]=1$ gives $f(x)$. This is why
the objective under the minimization in (4) agrees pointwise with the
original objective. No second moment is required.

## Depends on

- [Sampling vector](sampling-vector.md)
- [Weighted finite-sum objective](weighted-finite-sum-objective.md)
- [Expected value of a random variable](../../../Probability/foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

- [Integrability of a constant left multiple](../../../MeasureTheory/integration/integrability-of-sums-and-constant-multiples/integrable-const-mul.md)
- [Integrability of a finite pointwise sum](../../../MeasureTheory/integration/integrability-of-sums-and-constant-multiples/integrable-finset-sum.md)
- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)

## Sources

- R. M. Gower, N. Loizou, X. Qian, A. Sailanbayev, E. Shulgin, and
  P. Richtárik, [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4),
  arXiv:1901.09401v4, Section 1.2, the value-unbiasedness claim in the text
  after equation (4) and before equation (5).
