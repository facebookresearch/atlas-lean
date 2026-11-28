# Lebesgue integral

Let $(X, \mathcal{M}, \mu)$ be a measure space. For a measurable $f \colon X \to [0, \infty]$, $\int f \, d\mu$ is the
supremum of $\sum_j c_j \mu(A_j)$ over the simple functions $\sum_j c_j \chi_{A_j} \le f$ with
$A_1, \ldots, A_m \in \mathcal{M}$ disjoint and $c_1, \ldots, c_m \in [0, \infty)$. For a measurable
$f \colon X \to [-\infty, \infty]$ with $\int f^+ \, d\mu$ or $\int f^- \, d\mu$ finite,
$\int f \, d\mu = \int f^+ \, d\mu - \int f^- \, d\mu$, and for a measurable $f \colon X \to \mathbb{C}$ with
$\int |f| \, d\mu < \infty$, $\int f \, d\mu = \int \operatorname{Re} f \, d\mu + i \int \operatorname{Im} f \, d\mu$.

## Idea

The integral of a nonnegative function is approximated from below by integrals of simple functions, which only involve
measures of sets: Lebesgue's idea is to partition the range of $f$ rather than its domain. The integral is monotone,
also when the inequality holds only almost everywhere and on integrable real functions, and satisfies
$|\int f \, d\mu| \le \int |f| \, d\mu$. On a finite measure space constant functions are integrable, and a
constant $c$ has integral $\mu(X) c$; a constant $c \ge 0$ on a measurable set $B$ has integral $c \, \mu(B)$.
A nonnegative measurable function has integral $0$
exactly when it vanishes almost everywhere, and for an integrable real function that is nonnegative almost everywhere
the two integrals agree. These are the card's other statements. It is also positively homogeneous and additive; additivity
takes the monotone convergence theorem to prove. Unlike the Riemann integral, it is defined for the indicator of the
rationals in $[0, 1]$, with value $0$, and it behaves well under limits, by the monotone convergence theorem, Fatou's
lemma and the dominated convergence theorem.

## Statements

- [Lebesgue integral](lebesgue-integral.md)
- [Monotonicity of the integral](lintegral-mono.md): for functions with values in $[0, \infty]$.
- [Monotonicity of the integral almost everywhere](lintegral-mono-ae.md): the same when the inequality holds only almost everywhere.
- [A nonnegative function with integral zero vanishes almost everywhere](lintegral-eq-zero-iff.md): characterises the nonnegative measurable functions with integral zero.
- [Monotonicity of the integral of integrable functions](integral-mono.md): for integrable functions with values in an ordered space such as $\mathbb{R}$.
- [Norm of an integral](norm-integral-le-integral-norm.md): the bound $\|\int f \, d\mu\| \le \int \|f\| \, d\mu$, for functions with values in a normed space.
- [Integral of a nonnegative integrable function](of-real-integral-eq-lintegral-of-real.md): for an integrable real function that is nonnegative almost everywhere, the integral of real functions and the integral of functions with values in $[0, \infty]$ agree.
- [Integral of a constant on a set](lintegral-indicator-const.md): the integral of $c$ times the indicator of a measurable set $B$ is $c \, \mu(B)$.
- [Constant functions are integrable on a finite measure space](integrable-const.md): so that the integral of a constant below is that of an integrable function.
- [Integral of a constant](integral-const.md): for the Bochner integral, a constant $c$ has integral $\mu(X) c$ when $\mu(X) < \infty$, which is $c$ on a probability space, and $0$ when $\mu(X) = \infty$; the nonnegative integral of a constant $c \ge 0$ is $c \, \mu(X)$ in $[0, \infty]$.

## Background

- [Measures](../../../measures/measures-and-countable-additivity/measures/README.md): measures
- [Measurable functions](../../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/README.md): measurability

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definition 3.3 with result 3.9, Definitions 3.18 and 6.21, and results 3.22 and 3.23 (version read: the open-access PDF dated 12 June 2026).
