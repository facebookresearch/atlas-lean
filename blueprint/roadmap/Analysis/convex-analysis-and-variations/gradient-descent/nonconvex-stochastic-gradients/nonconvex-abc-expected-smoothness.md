# Nonconvex ABC expected smoothness

Let $f:\mathbb R^d\to\mathbb R$ be differentiable and bounded below, with
finite infimum $f_{\inf}=\inf_{y\in\mathbb R^d} f(y)\in\mathbb R$. Let
$g:\mathbb R^d\times\Omega\to\mathbb R^d$ be a pointwise unbiased stochastic
gradient oracle for $f$ on a probability space $(\Omega,\mathcal F,P)$.

The oracle satisfies **ABC expected smoothness** if there exist nonnegative
real constants $A,B,C$ such that, for every fixed $x\in\mathbb R^d$, the
function $\omega\mapsto\|g(x,\omega)\|_2^2$ is measurable and $P$-integrable
and satisfies

$$
\mathbb E_P[\|g(x,\cdot)\|_2^2]
\le 2A\bigl(f(x)-f_{\inf}\bigr)+B\|\nabla f(x)\|_2^2+C.
$$

The expectation on the left is the real integral of the squared Euclidean
norm $\|g(x,\omega)\|_2^2=\sum_{j=1}^d g_j(x,\omega)^2$ with respect to
$P$. The same three constants work for all $x$. The infimum need not be
attained, and $f$ need not be convex. The paper's separate Assumption 1 also
requires a Lipschitz gradient; that is not part of this second-moment condition.

This is a second-moment bound at one query point. The expected-smoothness
inequality in Gower et al., equation (7), instead bounds the squared difference
between the stochastic gradients at $x$ and at a fixed global minimizer,
using the same draw for both gradients.

## Depends on

- [Pointwise unbiased stochastic gradient oracle](pointwise-unbiased-stochastic-gradient-oracle.md)
- [Expected value of a random variable](../../../../Probability/foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Sources

- Ahmed Khaled and Peter Richtárik, [*Better Theory for SGD in the Nonconvex World*](https://arxiv.org/html/2002.03329v3#Thmasm2),
  arXiv:2002.03329v3, Section 4.2, Assumption 2 (ES), with the objective
  and oracle setup in Section 1.
- For the distinct same-draw condition: Robert M. Gower et al.,
  [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4#S2.E7),
  arXiv:1901.09401v4, Section 2.1, Assumption 2.1, equation (7).
