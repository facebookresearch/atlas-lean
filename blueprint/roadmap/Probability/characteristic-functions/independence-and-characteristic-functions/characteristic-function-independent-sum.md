# Characteristic function of a sum of independent random variables

Let $X_1$ and $X_2$ be independent real random variables with characteristic functions $\varphi_1$ and
$\varphi_2$. Then $X_1 + X_2$ has characteristic function $t \mapsto \varphi_1(t) \, \varphi_2(t)$.

## Proof

$e^{it(X_1 + X_2)} = e^{itX_1} e^{itX_2}$. The functions $g, h \in \{\cos(t \, \cdot), \sin(t \, \cdot)\}$ are
continuous, hence Borel measurable, and bounded by $1$, so each $g(X_1) h(X_2)$ is integrable:
$E|g(X_1) h(X_2)| \le E 1 = 1$, by monotonicity of the integral and since a constant is its own expected value.
Expanding both factors into real and imaginary parts and using linearity of the expected value writes
$E e^{it(X_1 + X_2)}$ as a combination of the four expected values $E[g(X_1) h(X_2)]$. For independent random variables
and bounded measurable $g$ and $h$, $E[g(X_1) h(X_2)] = E g(X_1) \, E h(X_2)$, and recombining the four products gives
$E e^{itX_1} \, E e^{itX_2}$.

## Depends on

- [Characteristic function of a random variable](../characteristic-functions-of-finite-measures/characteristic-function/characteristic-function-random-variable.md)
- [Independence of σ-fields, random variables and events](../../foundations/independent-events-and-random-variables/independence/independence-sigma-fields.md)

## Proof depends on

- [Expectation of a product of independent functions factors](../../laws-of-large-numbers/kolmogorov-s-three-series-theorem/three-series-theorem/integral-mul-of-indep-comp.md)
- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)
- [Continuous maps are Borel measurable](../../../MeasureTheory/measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/borel-measurable.md)
- [Monotonicity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Integral of a constant](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 3.3.2 (version read: the author's January 2019 PDF).
