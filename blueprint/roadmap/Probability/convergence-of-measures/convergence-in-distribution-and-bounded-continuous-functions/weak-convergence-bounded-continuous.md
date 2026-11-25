# Convergence in distribution through bounded continuous functions

Let $X_n$, $1 \le n \le \infty$, be real random variables, possibly defined on different probability
spaces, with distribution functions $F_n(x) = P(X_n \le x)$. Write $X_n \Rightarrow X_\infty$ if $F_n(y) \to F_\infty(y)$
at every point $y$ where $F_\infty$ is continuous. Then $X_n \Rightarrow X_\infty$ if and only if
$E g(X_n) \to E g(X_\infty)$ for every bounded continuous function $g \colon \mathbb R \to \mathbb R$.

## Proof

A bounded Borel function $g$ of a random variable $X$ has an expected value: $E|g(X)| \le \sup |g|$, by monotonicity of
the integral and since a constant is its own expected value. Suppose $X_n \Rightarrow X_\infty$. The Skorokhod
representation gives random variables $Y_n$ with $Y_n \to Y_\infty$ almost surely and with the distribution functions of
the $X_n$, hence with their laws, since a probability measure on $\mathbb R$ is determined by its distribution function.
So the random variables $g(Y_n)$, measurable because $g$ is continuous, converge to $g(Y_\infty)$ almost surely, hence
in probability, since almost sure convergence implies convergence in probability, and the bounded convergence theorem
gives $E g(Y_n) \to E g(Y_\infty)$. By the change of variables formula, $E g(X)$ depends only on the distribution of
$X$, so $E g(X_n) = E g(Y_n)$ for every $n$. Conversely, for $x \in \mathbb R$ and $\varepsilon > 0$ let
$g_{x,\varepsilon}$ be $1$ on $(-\infty, x]$, $0$ on $[x + \varepsilon, \infty)$ and linear in between. Since
$1_{(-\infty, x]} \le g_{x,\varepsilon} \le 1_{(-\infty, x + \varepsilon]}$, monotonicity of the expected value gives
$\limsup_n P(X_n \le x) \le \lim_n E g_{x,\varepsilon}(X_n) = E g_{x,\varepsilon}(X_\infty) \le P(X_\infty \le x + \varepsilon)$
and, in the same way,
$\liminf_n P(X_n \le x) \ge \lim_n E g_{x - \varepsilon,\varepsilon}(X_n) \ge P(X_\infty \le x - \varepsilon)$. At a
continuity point $x$ of $F_\infty$, letting $\varepsilon \downarrow 0$ gives $F_n(x) \to F_\infty(x)$.

## Depends on

- [Expected value of a random variable](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)
- [Probability measure](../../foundations/probability-measures/is-probability-measure.md)

## Proof depends on

- [Skorokhod representation on the real line](../skorokhod-representation-on-the-real-line/skorokhod-representation.md)
- [Change of variables formula for expected values](../../foundations/laws-of-random-variables-and-identical-distribut/change-of-variables/expectation-change-of-variables.md)
- [Convergence in probability via subsequential a.s. convergence](../convergence-in-probability/convergence-in-probability-iff-subsequen.md)
- [Bounded convergence theorem](../../../MeasureTheory/integration/bounded-convergence-theorem/tendsto-integral-of-bounded-convergence.md)
- [Construction of measures on ℝ](../../foundations/probability-measures-from-distribution-functions/stieltjes-measure-construction.md)
- [Monotonicity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-mono.md)
- [Continuous maps are Borel measurable](../../../MeasureTheory/measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/borel-measurable.md)
- [Monotonicity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Integral of a constant](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 3.2 (weak convergence) and Theorem 3.2.9 (version read: the author's January 2019 PDF).
