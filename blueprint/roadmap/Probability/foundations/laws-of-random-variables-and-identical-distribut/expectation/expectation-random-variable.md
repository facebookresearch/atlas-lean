# Expected value of a random variable

Let $X$ be a real random variable on a probability space $(\Omega, \mathcal F, P)$. If $X \ge 0$, its
*expected value* is $EX = \int_\Omega X \, dP$, which always exists in $[0, \infty]$. In general, with
$X^+ = \max(X, 0)$ and $X^- = \max(-X, 0)$, the expected value of $X$ exists and equals $EX = EX^+ - EX^-$ whenever
$EX^+ < \infty$ or $EX^- < \infty$. In particular $EX$ exists and is finite when $E|X| < \infty$, that is, when $X$
is integrable. $EX$ is also called the mean of $X$.

## Depends on

- [Probability measure](../../probability-measures/is-probability-measure.md)
- [Lebesgue integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lebesgue-integral.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 1.6, definition of the expected value (version read: the author's January 2019 PDF).
