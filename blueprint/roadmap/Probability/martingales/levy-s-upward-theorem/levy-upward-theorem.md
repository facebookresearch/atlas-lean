# Lévy's upward theorem

Let $(\mathcal F_n)_{n \ge 0}$ be an increasing sequence of σ-fields on a probability space
$(\Omega, \mathcal F, P)$, let $\mathcal F_\infty = \sigma\big(\bigcup_n \mathcal F_n\big)$, and let $X$ be a random variable with
$E|X| < \infty$. Then $E(X \mid \mathcal F_n) \to E(X \mid \mathcal F_\infty)$ almost surely and in $L^1$ as $n \to \infty$.

## Proof

By the tower property, $Y_n = E(X \mid \mathcal F_n)$ is a martingale, and each $Y_n$ is the conditional expectation of
the integrable $X$ given $\mathcal F_n$. A martingale of this form is uniformly integrable and converges almost surely
and in $L^1$. Its limit can be taken to be $Y_\infty = \limsup_n Y_n$ where this is finite and $0$ elsewhere, which is
$\mathcal F_\infty$-measurable, as suprema and infima of countably many measurable functions are measurable. For
$A \in \mathcal F_m$ and $n \ge m$, $\int_A X \, dP = \int_A Y_n \, dP$. By linearity of the integral, the bound
$|\int Z \, dP| \le \int |Z| \, dP$ and monotonicity,
$\big|\int_A Y_n \, dP - \int_A Y_\infty \, dP\big| \le E|Y_n - Y_\infty| \to 0$, so letting $n \to \infty$ gives
$\int_A X \, dP = \int_A Y_\infty \, dP$. Let $\mathcal L$ be the set of $A \in \mathcal F_\infty$ for which this holds.
It contains $\emptyset$ and $\Omega$, which lie in $\mathcal F_0$, and it is closed under complements, since
$\int_{\Omega \setminus A} Z \, dP = \int_\Omega Z \, dP - \int_A Z \, dP$ for integrable $Z$. It is closed under
countable disjoint unions, since $A \mapsto \int_A Z \, dP$ is countably additive for integrable $Z$: for disjoint
$A_1, A_2, \dots$, additivity of the integral and the monotone convergence theorem, applied to
$Z^+ 1_{A_1 \cup \dots \cup A_k}$ and to $Z^- 1_{A_1 \cup \dots \cup A_k}$, give
$\int_{\bigcup_i A_i} Z^\pm \, dP = \sum_i \int_{A_i} Z^\pm \, dP$, and both sums are finite. As $\mathcal L$ contains
the π-system $\bigcup_m \mathcal F_m$, which generates $\mathcal F_\infty$, Dynkin's π–λ theorem gives
$\mathcal L = \mathcal F_\infty$. So $Y_\infty$ is a version of $E(X \mid \mathcal F_\infty)$, and every version equals
$Y_\infty$ almost surely.

## Depends on

- [Conditional expectation given a σ-field](../../foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)
- [Expected value of a random variable](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

- [Tower property of conditional expectation](../../foundations/conditional-expectation/tower-property/tower-property.md)
- [Martingales, submartingales and supermartingales](../martingales-submartingales-and-supermartingales/martingale.md)
- [Equivalent conditions for uniform integrability of a martingale](../martingale-convergence-theorems/uniform-integrable-tfae-2.md)
- [Dynkin's π–λ theorem](../../../MeasureTheory/measurable-spaces/pi-systems-and-the-theorem/dynkin-s-pi-lambda-theorem/induction-on-inter.md)
- [Norm of an integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/norm-integral-le-integral-norm.md)
- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)
- [Monotonicity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Additivity and positive homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-nonnegative-additive-homogeneous.md)
- [Monotone convergence theorem with suprema](../../../MeasureTheory/integration/monotone-convergence-theorem/lintegral-i-sup.md)
- [Uniqueness of the conditional expectation](../../foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/ae-eq-cond-exp-of-forall-set-integral-eq.md)
- [Suprema of sequences of measurable functions are measurable](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/i-sup.md)
- [Infima of sequences of measurable functions are measurable](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/i-inf.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 4.6.8 (version read: the author's January 2019 PDF).
