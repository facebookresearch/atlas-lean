# Curtate lifetime as a tail sum

Let $T$ be a random variable with values in $[0, \infty]$ and let $\lfloor T \rfloor$ be its integer part, with $\lfloor \infty \rfloor = \infty$. Then

$$\mathbb E\,\lfloor T \rfloor = \sum_{k=1}^\infty \mathbb P(T \ge k) \qquad \text{in } [0, \infty],$$

because $\lfloor T \rfloor = \sum_{k \ge 1} \mathbf 1\{T \ge k\}$ pointwise and expectation commutes with sums of nonnegative terms. Applied to the future lifetime $T_x$ of a life aged $x$, this gives the curtate expectation of life $e_x = \mathbb E\,\lfloor T_x \rfloor = \sum_{k \ge 1} \mathbb P(T_x \ge k)$, which equals $\sum_{k \ge 1} {}_k p_x$ with ${}_k p_x = \mathbb P(T_x > k)$ when $T_x$ has no atoms at the integers.

## Proof depends on

- [Monotone convergence theorem](../../../MeasureTheory/integration/monotone-convergence-theorem/monotone-convergence-integrals.md)
- [Additivity and positive homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-nonnegative-additive-homogeneous.md)

## Sources

- D. C. M. Dickson, M. R. Hardy and H. R. Waters, *Actuarial Mathematics for Life Contingent Risks*, Cambridge University Press, Chapter 2 (curtate future lifetime and the curtate expectation of life)
