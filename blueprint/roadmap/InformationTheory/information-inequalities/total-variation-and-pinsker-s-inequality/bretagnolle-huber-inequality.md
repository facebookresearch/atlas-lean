# Bretagnolle–Huber inequality

Let $P$ and $Q$ be probability measures on a measurable space $(\Omega, \mathcal F)$ and let $A \in \mathcal F$.
Then

$$
P(A) + Q(\Omega \setminus A) \ge \tfrac12 \exp\big(-D(P \,\|\, Q)\big),
$$

where $D(P \,\|\, Q) \in [0, \infty]$ is the relative entropy of $P$ with respect to $Q$ and $\exp(-\infty) = 0$;
both sides are real numbers in $[0, 2]$.

The bound is trivial when $D(P \,\|\, Q) = \infty$, in particular when $P$ is not absolutely continuous with
respect to $Q$. Applied to $Q$, $P$ and $\Omega \setminus A$, it gives the same lower bound with $D(Q \,\|\, P)$.
In a test between $P$ and $Q$ that decides for $Q$ on $A$, the left side is the sum of the two error
probabilities.

## Proof

Notation. For $b \in [0, \infty]$ let $\bar b \in [0, \infty)$ be $b$ if $b < \infty$ and $0$ if $b = \infty$; for
$a \in \mathbb{R}$ let $a^+ = \max(a, 0) \in [0, \infty)$. Write $a \wedge b$ and $a \vee b$ for the minimum and the
maximum, $\sqrt{b} = b^{1/2}$ for $b \in [0, \infty]$, and, for a measurable set $B$ and $c \in [0, \infty]$,
$c \, \mathbf{1}_B$ for the function equal to $c$ on $B$ and to $0$ elsewhere ($\mathbf{1}_B$ when $c = 1$).
The functions below built from $p$, $q$ and $X$, such as $p \wedge q$, $\sqrt{pq}$, $e^X$ and $(e^X)^+$, are
measurable: a continuous map applied to a measurable function gives a measurable function, as continuous maps are
Borel measurable and a composition of measurable maps is measurable by definition, and pointwise minima, maxima and
products of measurable functions with values in $[0, \infty]$ are measurable. The logarithm on $\mathbb{R}$ (with
$\log 0 = 0$) and $b \mapsto \bar b$ on $[0, \infty]$ are measurable, so the log-likelihood ratio $\ell$ below is
measurable. Integrals of functions with values in $[0, \infty]$ are taken in $[0, \infty]$. Integrals of real functions are real
integrals of integrable functions; they appear from the paragraph on the divergence onwards, and pass to
$[0, \infty]$ through $a \mapsto a^+$, by the definition of the relative entropy and by the credited bridge between
the two integrals.

Densities. Let $\lambda = P + Q$, a finite measure. The finite measures $P$ and $Q$ have Lebesgue decompositions with
respect to $\lambda$; let $p = \frac{dP}{d\lambda}$ and $q = \frac{dQ}{d\lambda}$ be the Radon–Nikodym derivatives,
the measurable densities $\Omega \to [0, \infty]$ of those decompositions. As $P$ and $Q$ are absolutely continuous
with respect to $\lambda$, in $[0, \infty]$, $\int g \, dP = \int p \, g \, d\lambda$ and
$\int g \, dQ = \int q \, g \, d\lambda$ for every measurable $g \colon \Omega \to [0, \infty]$. With
$g = \mathbf{1}_B$ for a measurable set $B$, and $\int \mathbf{1}_B \, dP = P(B)$, this gives
$P(B) = \int p \, \mathbf{1}_B \, d\lambda$ and $Q(B) = \int q \, \mathbf{1}_B \, d\lambda$; with $B = \Omega$,
$\int p \, d\lambda = \int q \, d\lambda = 1$. As $\infty \, \mathbf{1}_{\{p = \infty\}} \le p$,
$\infty \cdot \lambda(\{p = \infty\}) = \int \infty \, \mathbf{1}_{\{p = \infty\}} \, d\lambda \le \int p \, d\lambda = 1$,
so $\lambda(\{p = \infty\}) = 0$, and likewise $\lambda(\{q = \infty\}) = 0$.

Overlap. The function $(p \wedge q) \, \mathbf{1}_A$ is measurable, and
$(p \wedge q) \, \mathbf{1}_A + (p \wedge q) \, \mathbf{1}_{\Omega \setminus A} = p \wedge q$. By monotonicity and
additivity of the integral, in $[0, \infty]$,

$$
P(A) + Q(\Omega \setminus A) = \int p \, \mathbf{1}_A \, d\lambda + \int q \, \mathbf{1}_{\Omega \setminus A} \, d\lambda
  \ge \int (p \wedge q) \, \mathbf{1}_A \, d\lambda + \int (p \wedge q) \, \mathbf{1}_{\Omega \setminus A} \, d\lambda
  = \int p \wedge q \, d\lambda.
$$

Cauchy–Schwarz. In $[0, \infty]$, $\sqrt{p \wedge q} \, \sqrt{p \vee q} = \sqrt{pq}$ and $p \vee q \le p + q$, so, by
monotonicity and additivity ($p$ is measurable),
$\int p \vee q \, d\lambda \le \int p \, d\lambda + \int q \, d\lambda = 2$. Hölder's inequality with exponents $2$ and
$2$, applied to the measurable functions $\sqrt{p \wedge q}$ and $\sqrt{p \vee q}$, gives, in $[0, \infty]$,

$$
\Big(\int \sqrt{pq} \, d\lambda\Big)^2 \le \int p \wedge q \, d\lambda \int p \vee q \, d\lambda
  \le 2 \int p \wedge q \, d\lambda,
$$

and, applied to $\sqrt{p}$ and $\sqrt{q}$, it gives
$\int \sqrt{pq} \, d\lambda \le \big(\int p \, d\lambda\big)^{1/2} \big(\int q \, d\lambda\big)^{1/2} = 1$.

The divergence. If $D(P \,\|\, Q) = \infty$ there is nothing to prove; let $D(P \,\|\, Q) < \infty$. By the
definition of the relative entropy, $P \ll Q$, the log-likelihood ratio $\ell = \log \overline{\frac{dP}{dQ}}$, a
measurable real function, is $P$-integrable, and $D(P \,\|\, Q) = \big(\int \ell \, dP\big)^+$, as both masses are
$1$; so $\int \ell \, dP \le D(P \,\|\, Q)$, an inequality between real numbers. The function
$q \, \mathbf{1}_{\{q = 0\}}$ is the zero function $0 \, \mathbf{1}_\Omega$, so
$Q(\{q = 0\}) = \int q \, \mathbf{1}_{\{q = 0\}} \, d\lambda = 0 \cdot \lambda(\Omega) = 0$; as $P \ll Q$, also
$P(\{q = 0\}) = 0$, so $\lambda(\{q = 0\}) = 0$. Let $G = \{0 < p < \infty, \ 0 < q < \infty\}$; then
$\Omega \setminus (G \cup \{p = 0\})$ lies in $\{p = \infty\} \cup \{q = 0\} \cup \{q = \infty\}$ and is
$\lambda$-null. In $[0, \infty]$, $\frac{dP}{dQ} = \frac{p}{q}$ $Q$-almost everywhere, hence $P$-almost everywhere
as $P \ll Q$, hence $\lambda$-almost everywhere; let $N$ be the $\lambda$-null set where it fails. On $G \setminus N$
the quotient $\frac{p}{q}$ is finite and positive with real value $\bar p / \bar q$, so $\ell = \log \bar p - \log \bar q$
there.

Let $X = -\frac12 \ell$, a measurable real function. It is $P$-integrable, as a constant multiple of the integrable
function $\ell$, and, by homogeneity of the integral, $\int X \, dP = -\frac12 \int \ell \, dP \ge -\frac12 D(P \,\|\, Q)$
in $\mathbb{R}$. On $G \setminus N$,
$e^X = \sqrt{\bar q / \bar p}$, so $p \, (e^X)^+ = \bar p \sqrt{\bar q / \bar p} = \sqrt{pq}$; on $\{p = 0\}$ both are
$0$. So $p \, (e^X)^+ \le \sqrt{pq}$ outside a $\lambda$-null set, and, in $[0, \infty]$, by the density formula with
$g = (e^X)^+$, monotonicity almost everywhere and the bound above,

$$
\int (e^X)^+ \, dP = \int p \, (e^X)^+ \, d\lambda \le \int \sqrt{pq} \, d\lambda \le 1.
$$

So $e^X$, a measurable real function whose absolute value $(e^X)^+$ has finite integral, is $P$-integrable, and its
real integral satisfies $\big(\int e^X \, dP\big)^+ = \int (e^X)^+ \, dP \le \int \sqrt{pq} \, d\lambda$.

The last step is in $\mathbb{R}$. Let $c = \int X \, dP$ and consider the real functions $g = X + (1 - c)$ and
$h = e^{-c} e^X$ on $\Omega$. The linear lower bound $x + 1 \le e^x$ for the exponential, at $x = X - c$, gives
$g \le h$ everywhere, as $e^{X - c} = e^{-c} e^X$. The function $h$ is $P$-integrable as a constant multiple of the
integrable function $e^X$; the constant function $1 - c$ is $P$-integrable as $P$ is finite, so $g$ is $P$-integrable
as the sum of two integrable functions. Monotonicity of the integral of integrable functions, then additivity,
homogeneity and the integral of a constant on the probability space $P$, give, in $\mathbb{R}$,

$$
\int X \, dP + (1 - c) = \int g \, dP \le \int h \, dP = e^{-c} \int e^X \, dP,
$$

that is, $1 \le e^{-c} \int e^X \, dP$; so $\int e^X \, dP \ge e^{c} \ge \exp\big(-\frac12 D(P \,\|\, Q)\big) > 0$.
Back in $[0, \infty]$, this gives
$\exp\big(-\frac12 D(P \,\|\, Q)\big) \le \big(\int e^X \, dP\big)^+ \le \int \sqrt{pq} \, d\lambda$, and squaring
and chaining with the two displays above,

$$
\exp\big(-D(P \,\|\, Q)\big) \le \Big(\int \sqrt{pq} \, d\lambda\Big)^2 \le 2 \int p \wedge q \, d\lambda
  \le 2 \, \big(P(A) + Q(\Omega \setminus A)\big).
$$

## Depends on

- [Relative entropy of measures](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/kl-div.md)
- [Probability measure](../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [σ-algebra](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/measurable-space.md)

## Proof depends on

- [Measurable function](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable.md)
- [Continuous maps are Borel measurable](../../../MeasureTheory/measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/borel-measurable.md)
- [Monotonicity of a measure](../../../MeasureTheory/measures/measures-and-countable-additivity/measures/measure-mono.md)
- [Countable subadditivity of a measure](../../../MeasureTheory/measures/measures-and-countable-additivity/measures/measure-i-union-le.md)
- [Almost everywhere](../../../MeasureTheory/measures/measures-and-countable-additivity/measures/ae.md)
- [σ-finite measure](../../../MeasureTheory/measures/measures-and-countable-additivity/measures/sigma-finite.md)
- [Lebesgue decomposition theorem](../../../MeasureTheory/absolute-continuity-densities/lebesgue-decomposition-of-measures/have-lebesgue-decomposition-of-sigma-finite.md)
- [Integrating against a Radon–Nikodym derivative](../../../MeasureTheory/absolute-continuity-densities/radon-nikodym-theorem/lintegral-rn-deriv-mul.md)
- [Radon–Nikodym derivative as a ratio of densities](../../../MeasureTheory/absolute-continuity-densities/radon-nikodym-theorem/rn-deriv-eq-div-rn-deriv-add.md)
- [Monotonicity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Monotonicity of the integral almost everywhere](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono-ae.md)
- [Additivity of the integral when one function is measurable](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/lintegral-add-left.md)
- [Integral of a constant on a set](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-indicator-const.md)
- [Integral of a nonnegative integrable function](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/of-real-integral-eq-lintegral-of-real.md)
- [Hölder's inequality for functions with values in $[0, \infty]$](../../../MeasureTheory/lp-spaces/h-lder-and-minkowski-inequalities-for-integrals/h-lder-s-inequality/lintegral-mul-le-lp-mul-lq.md)
- [Monotonicity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-mono.md)
- [Additivity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)
- [Integral of a constant](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)
- [The sum of two integrable functions is integrable](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integrable-add.md)
- [A constant multiple of an integrable function is integrable](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integrable-const-mul.md)
- [Constant functions are integrable on a finite measure space](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integrable-const.md)
- [Linear lower bound for the exponential](../../../Analysis/special-functions/elementary-transcendental-functions/add-one-le-exp.md)

## Informally uses

- [Common part of two probability measures](exists-le-le-measure-univ-eq.md): the overlap
  $\int p \wedge q$ that the proof bounds below.

## Background

- [Two-point testing bound](one-sub-total-variation-dist-le-add-comp.md) and
  [Pinsker's inequality for probability measures](of-real-two-mul-total-variation-dist-sq.md): together they give
  $P(A) + Q(\Omega \setminus A) \ge 1 - \sqrt{D(P \,\|\, Q)/2}$ when $D(P \,\|\, Q) < \infty$, which is better for
  small divergences but vacuous once $D(P \,\|\, Q) \ge 2$.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy,
  <https://tor-lattimore.com/downloads/book/book.pdf>), Theorem 14.2 (Bretagnolle–Huber inequality) and its proof
  at the end of Section 14.2, which the proof above follows, except that its last step integrates
  $e^y \ge 1 + y$ directly; Section 14.4 attributes the inequality to
  J. Bretagnolle and C. Huber, *Estimation des densités : risque minimax*, Z. Wahrscheinlichkeitstheorie verw.
  Gebiete 47 (1979), 119–137.
