# Doob's $L^p$ maximal inequality

Let $(X_n)_{n \ge 0}$ be a submartingale with respect to a filtration $(\mathcal F_n)_{n \ge 0}$, let
$n \ge 0$, put $\bar X_n = \max_{0 \le m \le n} X_m^+$, and let $1 < p < \infty$. Then, as an inequality in $[0, \infty]$,

$$E\big(\bar X_n^{\,p}\big) \le \Big(\frac{p}{p - 1}\Big)^p E\big((X_n^+)^p\big).$$

Consequently, if $(Y_n)_{n \ge 0}$ is a martingale and $Y_n^* = \max_{0 \le m \le n} |Y_m|$, then
$E\big(|Y_n^*|^p\big) \le \big(\frac{p}{p - 1}\big)^p E\big(|Y_n|^p\big)$.

## Proof

The second inequality is the first applied to $(|Y_n|)$, a submartingale because the absolute value is convex. For the
first, $(X_n^+)$ is a nonnegative submartingale, since $x \mapsto x^+$ is convex and nondecreasing, and Doob's maximal
inequality for nonnegative submartingales gives $\lambda P(\bar X_n \ge \lambda) \le E(X_n^+ ; \bar X_n \ge \lambda)$
for $\lambda > 0$. Fix $M > 0$. The running maximum $\bar X_n$ and $\bar X_n \wedge M$ are random variables, as the
supremum and the infimum of finitely many random variables, and $\{(\lambda, \omega) : \bar X_n(\omega) \ge \lambda\}$
is measurable for the product σ-field, as the preimage of the closed set $\{(u, v) : v \ge u\}$, a Borel set of
$\mathbb R^2$ and hence a set of its product σ-field, under the map
$(\lambda, \omega) \mapsto (\lambda, \bar X_n(\omega))$, which is measurable for the product σ-fields. By the
tail-integral formula and Tonelli's theorem,
$E((\bar X_n \wedge M)^p) = \int_0^M p \lambda^{p-1} P(\bar X_n \ge \lambda) \, d\lambda \le \int_0^M p \lambda^{p-2} E(X_n^+ ; \bar X_n \ge \lambda) \, d\lambda = \frac{p}{p-1} E\big(X_n^+ (\bar X_n \wedge M)^{p-1}\big)$,
and Hölder's inequality bounds the right side by
$\frac{p}{p-1} \big(E (X_n^+)^p\big)^{1/p} \big(E (\bar X_n \wedge M)^p\big)^{(p-1)/p}$. If $E((X_n^+)^p) = \infty$
there is nothing to prove. If $E((\bar X_n \wedge M)^p) = 0$, the bound
$E((\bar X_n \wedge M)^p) \le \big(\frac{p}{p-1}\big)^p E((X_n^+)^p)$ holds trivially. Otherwise the last factor is
positive and finite, since $E((\bar X_n \wedge M)^p) \le E(M^p) = M^p$ by monotonicity of the integral, and dividing by
it gives the same bound. Letting $M \uparrow \infty$ with the monotone convergence theorem gives the claim.

## Depends on

- [Martingales, submartingales and supermartingales](../martingales-submartingales-and-supermartingales/martingale.md)
- [Expected value of a random variable](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

- [Convex functions of martingales are submartingales](../convex-functions-of-martingales/submartingale-comp-convex.md)
- [Convex nondecreasing functions preserve submartingales](../convex-functions-of-martingales/comp-convex-of-monotone-on.md)
- [Doob's maximal inequality for nonnegative submartingales](maximal-ineq.md)
- [Layer-cake formula for powers](../../../MeasureTheory/integration/layer-cake-formula/lintegral-rpow-eq-lintegral-meas-le-mul.md)
- [Tonelli's theorem for iterated integrals](../../../MeasureTheory/integration/iterated-integrals/lintegral-lintegral-swap.md)
- [Hölder's inequality for functions with values in $[0, \infty]$](../../../MeasureTheory/lp-spaces/h-lder-and-minkowski-inequalities-for-integrals/h-lder-s-inequality/lintegral-mul-le-lp-mul-lq.md)
- [Monotone convergence theorem with suprema](../../../MeasureTheory/integration/monotone-convergence-theorem/lintegral-i-sup.md)
- [Suprema of sequences of measurable functions are measurable](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/i-sup.md)
- [Infima of sequences of measurable functions are measurable](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/i-inf.md)
- [Monotonicity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Borel σ-algebra of a countable product of second-countable spaces](../../../MeasureTheory/measurable-spaces/borel-algebras-and-continuous-maps/borel-sets-of-countable-products/pi-borel-space.md)
- [Integral of a constant](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 4.4.4, with the notation of Theorem 4.4.2 (version read: the author's January 2019 PDF).
