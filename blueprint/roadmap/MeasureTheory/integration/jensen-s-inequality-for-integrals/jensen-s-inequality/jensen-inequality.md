# Jensen's inequality

Let $\varphi \colon \mathbb{R} \to \mathbb{R}$ be convex, that is,
$\varphi(\lambda x + (1 - \lambda) y) \le \lambda \varphi(x) + (1 - \lambda) \varphi(y)$ for all $x, y \in \mathbb{R}$
and $\lambda \in [0, 1]$. Let $X$ be a real random variable on a probability space $(\Omega, \mathcal{F}, P)$ with
$E|X| < \infty$ and $E|\varphi(X)| < \infty$, where $E$ denotes the integral with respect to $P$. Then

$$\varphi(EX) \le E\varphi(X).$$

## Proof

Let $c = EX$. For $x < c < y$, write $c = \lambda x + (1 - \lambda) y$ with $\lambda = (y - c)/(y - x) \in (0, 1)$; then
convexity gives $\varphi(c) \le \lambda \varphi(x) + (1 - \lambda) \varphi(y)$, which rearranges to

$$\frac{\varphi(c) - \varphi(x)}{c - x} \le \frac{\varphi(y) - \varphi(c)}{y - c}.$$

So $a = \sup_{x < c} (\varphi(c) - \varphi(x))/(c - x)$ is finite and at most every quotient on the right, which gives
$\varphi(x) \ge \varphi(c) + a(x - c)$ for every $x \in \mathbb{R}$. Hence $\varphi(X) \ge \varphi(c) + a(X - c)$ on
$\Omega$, where the right side is integrable since $P(\Omega) = 1$. Monotonicity of the integral, then additivity,
homogeneity and the integral of a constant, which on the probability space is the constant itself, give
$E\varphi(X) \ge \varphi(c) + a(EX - c) = \varphi(EX)$.

## Depends on

- [Lebesgue integral](../../nonnegative-lebesgue-integral/lebesgue-integral/lebesgue-integral.md)
- [Measurable function](../../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable.md)
- [Measure](../../../measures/measures-and-countable-additivity/measures/measure.md)

## Proof depends on

- [Monotonicity of the integral of integrable functions](../../nonnegative-lebesgue-integral/lebesgue-integral/integral-mono.md)
- [Additivity of the integral of integrable functions](../../nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)
- [Integral of a constant](../../nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 1.6.2 (version read: the author's January 2019 PDF).
