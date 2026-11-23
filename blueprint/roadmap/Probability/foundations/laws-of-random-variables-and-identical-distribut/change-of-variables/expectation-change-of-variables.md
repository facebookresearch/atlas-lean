# Change of variables formula for expected values

Let $X$ be a random element of a measurable space $(S, \mathcal S)$, defined on a probability space
$(\Omega, \mathcal F, P)$, with distribution $\mu(A) = P(X \in A)$ for $A \in \mathcal S$, and let $f \colon S \to \mathbb R$
be measurable for $\mathcal S$ and the Borel sets of $\mathbb R$. If $f \ge 0$ or $E|f(X)| < \infty$, then

$$E f(X) = \int_S f(y) \, \mu(dy).$$

In the first case both sides may equal $+\infty$; in the second, $f$ is $\mu$-integrable.

## Proof

For $f = 1_B$ with $B \in \mathcal S$ both sides equal $P(X \in B) = \mu(B)$. Linearity of the integral
extends the identity to nonnegative simple functions. A measurable $f \ge 0$ is the pointwise limit of an increasing
sequence of nonnegative simple functions $f_k$; then $f_k(X) \uparrow f(X)$, and the monotone convergence theorem on
both sides gives the identity. If $E|f(X)| < \infty$, the nonnegative case for $|f|$ shows
$\int_S |f| \, d\mu = E|f(X)| < \infty$, and applying it to $f^+$ and $f^-$ and subtracting gives the identity.

## Depends on

- [Expected value of a random variable](../expectation/expectation-random-variable.md)
- [Law of a random element](../../probability-measures/probability-measure-map.md)
- [Lebesgue integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lebesgue-integral.md)

## Proof depends on

- [Indicator function of a set](../../../../Algebra/algebraic-identities/indicator-one.md)
- [Approximation of nonnegative measurable functions by simple functions](../../../../MeasureTheory/integration/approximation-by-simple-functions/exists-monotone-tendsto.md)
- [Monotone convergence theorem with suprema](../../../../MeasureTheory/integration/monotone-convergence-theorem/lintegral-i-sup.md)
- [Additivity and positive homogeneity of the integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-nonnegative-additive-homogeneous.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 1.6.9 (version read: the author's January 2019 PDF).
