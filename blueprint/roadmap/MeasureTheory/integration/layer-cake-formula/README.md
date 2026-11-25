# Layer-cake formula

Let $\mu$ be a measure, $f \ge 0$ almost everywhere and almost everywhere measurable, and $p > 0$. Then
$\int f^p \, d\mu = p \int_0^\infty t^{p-1} \mu(\{f \ge t\}) \, dt$. For $p = 1$ it writes the integral of $f$ as the
integral of the measures of its upper level sets, $\int f \, d\mu = \int_0^\infty \mu(\{f \ge t\}) \, dt$, and for a
random variable $X \ge 0$ it gives $E X^p = \int_0^\infty p t^{p-1} P(X \ge t) \, dt$.

## Idea

Replace $f$ by a nonnegative measurable function equal to it almost everywhere, which changes neither side. Writing
$f(x)^p = \int_0^{f(x)} p t^{p-1} \, dt = \int_0^\infty p t^{p-1} \chi_{\{t \le f(x)\}} \, dt$ and exchanging the two
integrals gives the formula: the region under the graph of $f$ is cut into horizontal layers, the layer at height $t$
having measure $\mu(\{f \ge t\})$. Height $t$ for $f$ is height $t^p$ for $f^p$, and $p t^{p-1} \, dt = d(t^p)$ is the
change of that second height. The exchange is Tonelli's theorem, which needs s-finite measures, so $\mu$ is first
reduced to that case. If $\mu(\{f \ge t\}) = \infty$ for some $t > 0$, both sides are infinite; otherwise the
restriction of $\mu$ to $\{f > 0\}$, the union of the sets $\{f \ge 1/n\}$ of finite measure, is σ-finite, and
$\{f \le 0\}$ contributes to neither side. Moments are thereby computed from tail probabilities, and $L^p$ norms from
distribution functions.

## Statements

- [Layer-cake formula for powers](lintegral-rpow-eq-lintegral-meas-le-mul.md)

## Background

- [Fubini–Tonelli theorem for iterated integrals](../iterated-integrals/README.md): used in the proof

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Lemma 2.2.13, with $P(Y > y)$ in place of $\mu(\{f \ge t\})$ (version read: the author's January 2019 PDF).
