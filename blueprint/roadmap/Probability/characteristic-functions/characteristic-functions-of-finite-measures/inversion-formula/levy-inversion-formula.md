# Inversion formula for characteristic functions

Let $\mu$ be a probability measure on $\mathbb R$ with characteristic function
$\varphi(t) = \int e^{itx} \, \mu(dx)$, and let $a < b$ be real numbers. Then

$$\lim_{T \to \infty} \frac{1}{2\pi} \int_{-T}^{T} \frac{e^{-ita} - e^{-itb}}{it} \, \varphi(t) \, dt = \mu((a, b)) + \tfrac{1}{2} \mu(\{a, b\}),$$

and in particular the limit exists. The integrand, given its limiting value $b - a$ at $t = 0$, is bounded by $b - a$.

## Proof

Since $|e^{-ita} - e^{-itb}| = |e^{it(b - a)} - 1| = 2 |\sin(t (b - a) / 2)| \le |t| (b - a)$ and
$|\varphi(t)| \le \int |e^{itx}| \, \mu(dx) = \mu(\mathbb R) = 1$, the integrand on the left has modulus at most
$b - a$. In the same way $(t, x) \mapsto \frac{e^{it(x - a)} - e^{it(x - b)}}{it}$ has modulus at most $b - a$ on
$[-T, T] \times \mathbb R$. It is continuous there, with the value $b - a$ at $t = 0$, hence measurable for the Borel
σ-field, which is the product σ-field; being bounded, it is integrable for the product of Lebesgue measure on $[-T, T]$
and $\mu$, a finite measure, by monotonicity of the integral and the integral of a constant. So Fubini's theorem lets
one integrate in $t$ first. For real $c$, $\frac{e^{itc}}{it} = \frac{\sin(tc)}{t} - i \, \frac{\cos(tc)}{t}$. So, for
fixed $x$, the cosine terms of $\frac{e^{it(x - a)} - e^{it(x - b)}}{it}$ give its imaginary part,
$-\frac{\cos(t(x - a)) - \cos(t(x - b))}{t}$, which is odd in $t$ and bounded by $b - a$, so it integrates to zero over
$[-T, T]$; and the sine terms give its real part $\frac{\sin(t(x - a)) - \sin(t(x - b))}{t}$, which is even in $t$. With
$S(R) = \int_0^R \frac{\sin u}{u} \, du$ and
$\int_{-T}^{T} \frac{\sin(tc)}{t} \, dt = 2 \operatorname{sgn}(c) \, S(T |c|)$, linearity of the integral turns the
expression inside the limit into
$\int \frac{1}{\pi} \big(\operatorname{sgn}(x - a) S(T |x - a|) - \operatorname{sgn}(x - b) S(T |x - b|)\big) \, \mu(dx)$.
Since $|\sin u / u| \le 1$, the bound $|\int f| \le \int |f|$, monotonicity of the integral and the integral of a
constant give $|S(R') - S(R)| \le |R' - R|$. So $S$ is continuous, with $S(0) = 0$, and the integrand
$x \mapsto \frac{1}{\pi} \big(\operatorname{sgn}(x - a) S(T |x - a|) - \operatorname{sgn}(x - b) S(T |x - b|)\big)$ is
continuous, hence Borel measurable. By the Dirichlet integral, $S(R) \to \frac{\pi}{2}$ as $R \to \infty$. So $S$ is
bounded on $[R_0, \infty)$ for some $R_0$, and on $[0, R_0]$ it is bounded by $R_0$, as $|S(R)| = |S(R) - S(0)| \le R$;
hence $S$ is bounded on $[0, \infty)$. The integrand is therefore bounded, and it tends to $1$ on $(a, b)$, to $\frac12$
at $a$ and at $b$, and to $0$ elsewhere. Along any sequence $T_k \to \infty$ this pointwise convergence implies
convergence in $\mu$-measure, and the bounded convergence theorem gives the limit.

## Depends on

- [Characteristic function of a random variable](../characteristic-function/characteristic-function-random-variable.md)
- [Probability measure](../../../foundations/probability-measures/is-probability-measure.md)
- [Lebesgue integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lebesgue-integral.md)
- [Lebesgue measure on the real line](../../../../MeasureTheory/lebesgue-measure/lebesgue-measure-on-euclidean-spaces/lebesgue-measure-on-the-real-line/lebesgue-measure.md)

## Proof depends on

- [Fubini's theorem for iterated integrals](../../../../MeasureTheory/integration/iterated-integrals/integral-integral-swap.md)
- [The Dirichlet integral](../../../../Analysis/special-functions/elementary-transcendental-functions/sine-integral/tendsto-sine-integral-at-top.md)
- [Convergence in probability via subsequential a.s. convergence](../../../convergence-of-measures/convergence-in-probability/convergence-in-probability-iff-subsequen.md)
- [Bounded convergence theorem](../../../../MeasureTheory/integration/bounded-convergence-theorem/tendsto-integral-of-bounded-convergence.md)
- [Additivity of the integral of integrable functions](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)
- [Continuous maps are Borel measurable](../../../../MeasureTheory/measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/borel-measurable.md)
- [Norm of an integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/norm-integral-le-integral-norm.md)
- [Monotonicity of the integral](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Monotonicity of the integral of integrable functions](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-mono.md)
- [Integral of a constant](../../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)
- [Borel σ-algebra of a countable product of second-countable spaces](../../../../MeasureTheory/measurable-spaces/borel-algebras-and-continuous-maps/borel-sets-of-countable-products/pi-borel-space.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 3.3.11, its proof and the remark after it (version read: the author's January 2019 PDF).
