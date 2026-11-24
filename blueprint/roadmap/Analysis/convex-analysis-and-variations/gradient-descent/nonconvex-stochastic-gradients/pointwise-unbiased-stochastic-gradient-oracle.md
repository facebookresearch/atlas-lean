# Pointwise unbiased stochastic gradient oracle

Let $f:\mathbb R^d\to\mathbb R$ be differentiable, let $(\Omega,\mathcal F,P)$
be a probability space, and let $g:\mathbb R^d\times\Omega\to\mathbb R^d$.
Write $\nabla f(x)$ for the Euclidean gradient, the vector representing the
Fréchet derivative by the dot product.

The map $g$ is a **pointwise unbiased stochastic gradient oracle** for $f$
if, for every fixed $x\in\mathbb R^d$ and every coordinate $j=1,\ldots,d$,
the function $\omega\mapsto g_j(x,\omega)$ is measurable for the Borel
$\sigma$-algebra on $\mathbb R$, is $P$-integrable, and satisfies

$$
\mathbb E_P[g_j(x,\cdot)]
=\int_\Omega g_j(x,\omega)\,dP(\omega)
=(\nabla f(x))_j.
$$

The vector expectation in $\mathbb E_P[g(x,\cdot)]=\nabla f(x)$ consists of
these real coordinate integrals. The query $x$ is deterministic; only the
oracle draw is averaged. This condition requires neither joint measurability
in $(x,\omega)$ nor independence of the coordinates. It imposes no
finite-sum model or rule for drawing samples at random iterates. It also
does not require $f$ to be bounded below or $\nabla f$ to be Lipschitz.

## Depends on

- [A Fréchet derivative given by a dot product is a gradient](../../../real-functions/multivariable-calculus/gradient/has-gradient-at-of-lp.md)
- [Probability measure](../../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [Measurable function](../../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable.md)
- [Expected value of a random variable](../../../../Probability/foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Sources

- Ahmed Khaled and Peter Richtárik, [*Better Theory for SGD in the Nonconvex World*](https://arxiv.org/html/2002.03329v3#S1.p2.2),
  arXiv:2002.03329v3, Section 1, the unbiasedness condition immediately after
  equation (2). The coordinate integrals make the paper's vector expectation
  explicit at a fixed input.
