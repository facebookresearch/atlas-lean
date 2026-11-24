# Characteristic function of a random variable

Let $X$ be a real random variable on a probability space $(\Omega, \mathcal F, P)$. Its *characteristic
function* is the function $\varphi \colon \mathbb R \to \mathbb C$ given by

$$\varphi(t) = E e^{itX} = E \cos(tX) + i \, E \sin(tX),$$

where the expected value of a complex random variable $Z$ is $EZ = E(\operatorname{Re} Z) + i \, E(\operatorname{Im} Z)$;
both expectations exist because $\cos(tX)$ and $\sin(tX)$ are bounded. The characteristic function of a probability
measure $\mu$ on $\mathbb R$ is $\varphi(t) = \int e^{itx} \, \mu(dx)$, the characteristic function of any random variable
with distribution $\mu$.

## Proof

Both expected values in the definition exist: $\cos(tX)$ and $\sin(tX)$ are random variables, since continuous functions
are Borel measurable, and their absolute values are at most $1$, so $E|\cos(tX)| \le E 1 = 1$ and $E|\sin(tX)| \le 1$,
by monotonicity of the integral and since a constant is its own expected value. The two descriptions agree. If $X$ has
distribution $\mu$, the change of variables formula, applied to the bounded Borel functions $x \mapsto \cos(tx)$ and
$x \mapsto \sin(tx)$, gives $E \cos(tX) = \int \cos(tx) \, \mu(dx)$ and $E \sin(tX) = \int \sin(tx) \, \mu(dx)$, so
$E e^{itX} = \int e^{itx} \, \mu(dx)$. In particular the characteristic function of a random variable depends only on
its distribution.

## Depends on

- [Expected value of a random variable](../../../foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)
- [Probability measure](../../../foundations/probability-measures/is-probability-measure.md)
- [Law of a random element](../../../foundations/probability-measures/probability-measure-map.md)
- [Lebesgue integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lebesgue-integral.md)

## Proof depends on

- [Change of variables formula for expected values](../../../foundations/laws-of-random-variables-and-identical-distribut/change-of-variables/expectation-change-of-variables.md)
- [Continuous maps are Borel measurable](../../../../MeasureTheory/measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/borel-measurable.md)
- [Monotonicity of the integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Integral of a constant](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 3.3.1, definition of the characteristic function (version read: the author's January 2019 PDF).
