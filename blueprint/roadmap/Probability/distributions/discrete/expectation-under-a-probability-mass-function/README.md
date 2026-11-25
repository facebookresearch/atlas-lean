# Expectation under a probability mass function

Let $p$ be a probability mass function on a set $\alpha$ carrying a σ-algebra in which singletons are measurable, and let $f : \alpha \to \mathbb{R}$. The expectation of $f$ under $p$ is the integral $\int f \, d\mu_p$ against the probability measure $\mu_p$ associated to $p$, with the convention that this integral is $0$ when $f$ is not integrable. For integrable $f$ it is the series $\sum_{a} p(a) f(a)$, and on a finite set it is the finite sum $\sum_{a \in \alpha} p(a) f(a)$. For $f$ with values in $[0, \infty]$ there is also the extended expectation $\sum_a p(a) f(a) \in [0, \infty]$, which needs no measurability or integrability hypothesis and takes the value $\infty$ when the sum diverges.

## Idea

The expectation is the probability-weighted average of the values of $f$: for a fair die and $f(a) = a$ it is $(1 + 2 + \dots + 6)/6 = 7/2$. On a finite set the finite-sum formula makes linearity, monotonicity and the change-of-variables formula $\mathbb{E}_{g_* p}[f] = \mathbb{E}_p[f \circ g]$ plain computations, with no integrability hypothesis, and gives the average $\frac{1}{|\alpha|} \sum_a f(a)$ under the uniform distribution. The real-valued expectation must give some value to functions whose mean diverges, and the value $0$ can mislead; the extended expectation avoids this for nonnegative functions by allowing $\infty$. On a finite set the two agree for natural-valued functions.

## Statements

- [Expectation under a probability mass function](expect.md)
- [Expectation on a finite type](expect-eq-sum.md): formula on a finite type
- [Expectation of a finitely supported distribution](expect-eq-sum-of-finite-support.md): formula for finitely supported laws
- [Expectation as a series](expect-eq-tsum.md): series formula
- [Expectation of a constant on a finite type](expect-const.md): basic property: constants
- [Additivity of expectation on a finite type](expect-add.md): basic property: additivity
- [Homogeneity of expectation on a finite type](expect-const-mul.md): basic property: homogeneity
- [Expectation of a scalar multiple](expect-smul.md): basic property: scalar multiples
- [Expectation of a finite sum](expect-sum.md): basic property: finite sums
- [Nonnegativity of expectation](expect-nonneg.md): basic property: nonnegativity
- [Monotonicity of expectation](expect-le-expect.md): basic property: monotonicity
- [Expectation of an indicator](expect-indicator-decide.md): basic property: indicators give probabilities
- [Change of variables for expectation](expect-map.md): change of variables
- [Expectation under the uniform distribution](expect-uniform-of-fintype.md): example: the uniform distribution
- [Extended expectation](expect-enn.md): extended-valued version
- [Extended expectation on a finite set](expect-enn-eq-sum.md): extended-valued version
- [Extended expectation under a finitely supported distribution](expect-enn-eq-sum-of-finite-support.md): extended-valued version
- [Extended expectation of a constant](expect-enn-const.md): extended-valued version
- [Additivity of extended expectation](expect-enn-add.md): extended-valued version
- [Extended expectation of a finite sum](expect-enn-sum.md): extended-valued version
- [Change of variables for extended expectation](expect-enn-map.md): extended-valued version
- [Extended expectation under the uniform distribution](expect-enn-uniform-of-fintype.md): extended-valued version
- [Extended and real expectations agree on natural-valued functions](expect-enn-nat-cast-to-real.md): agreement of the two versions
