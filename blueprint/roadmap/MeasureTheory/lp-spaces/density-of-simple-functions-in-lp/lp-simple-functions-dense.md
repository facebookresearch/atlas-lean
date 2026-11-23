# Simple functions are dense in $L^p$

Let $(X, \mathcal{M}, \mu)$ be a measure space, let $\mathbb{F}$ be $\mathbb{R}$ or $\mathbb{C}$, and let
$0 < p \le \infty$. Write $\mathcal{L}^p(\mu)$ for the set of measurable functions $h \colon X \to \mathbb{F}$ with
$\|h\|_p < \infty$, where $\|h\|_p = \big(\int |h|^p \, d\mu\big)^{1/p}$ if $p < \infty$ and
$\|h\|_\infty = \inf\{t > 0 : \mu(\{x : |h(x)| > t\}) = 0\}$. Then for every $f \in \mathcal{L}^p(\mu)$ and every
$\varepsilon > 0$ there is a simple function $g \in \mathcal{L}^p(\mu)$, that is, one with finitely many values,
such that $\|f - g\|_p < \varepsilon$.

The cited exercise states the paragraph above. In addition, for $p < \infty$ a simple function lies in
$\mathcal{L}^p(\mu)$ exactly when it is a linear combination $\sum_{j=1}^n a_j \chi_{E_j}$ with $a_j \in \mathbb{F}$
and measurable sets $E_j$ of finite measure; so for $1 \le p < \infty$ these combinations are dense in $L^p(\mu)$.

## Proof

For $p < \infty$, a combination $g = \sum_j a_j \chi_{E_j}$ with $\mu(E_j) < \infty$ is measurable and simple, and
$|g| \le \big(\sum_j |a_j|\big) \chi_E$ with $E = \bigcup_j E_j$ and $\mu(E) \le \sum_j \mu(E_j) < \infty$, so
$\int |g|^p \, d\mu \le \big(\sum_j |a_j|\big)^p \mu(E) < \infty$. Conversely, if $g \in \mathcal{L}^p(\mu)$ is simple
with distinct nonzero values $a_1, \ldots, a_n$, then $g = \sum_j a_j \chi_{E_j}$ with $E_j = \{g = a_j\}$
measurable, and $|a_j|^p \chi_{E_j} \le |g|^p$ gives $\mu(E_j) \le |a_j|^{-p} \int |g|^p \, d\mu < \infty$.

Now let $f \in \mathcal{L}^p(\mu)$. If $p = \infty$, let $M = \|f\|_\infty$: the set $N = \{|f| > M\}$ is the union of
the null sets $\{|f| > M + 1/n\}$, so it is null, and replacing $f$ by $f \chi_{X \setminus N}$ changes
$\|f - g\|_\infty$ for no $g$; we may therefore assume $|f| \le M$ everywhere. Write $f = u_1 - u_2 + i(u_3 - u_4)$,
where $u_1, u_2$ are the positive and negative parts of $\operatorname{Re} f$ and $u_3, u_4$ those of
$\operatorname{Im} f$, with $u_3 = u_4 = 0$ if $\mathbb{F} = \mathbb{R}$; these are measurable, being continuous
functions of $f$. For each $l$ take nonnegative measurable simple functions $s_{l,1} \le s_{l,2} \le \cdots$ that
increase to $u_l$ and converge uniformly on every set where $u_l$ is bounded by a finite constant, and put
$\varphi_k = s_{1,k} - s_{2,k} + i(s_{3,k} - s_{4,k})$. Each $\varphi_k$ is measurable and simple, $\varphi_k \to f$
pointwise, and $|\varphi_k| \le u_1 + u_2 + u_3 + u_4 \le 2|f|$.

If $p < \infty$, then $\varphi_k \in \mathcal{L}^p(\mu)$ and $|f - \varphi_k|^p \le 3^p |f|^p$, which is integrable;
by the dominated convergence theorem, $\int |f - \varphi_k|^p \, d\mu \to 0$, so $\|f - \varphi_k\|_p < \varepsilon$ for
large $k$. If $p = \infty$, then $u_l \le M$ everywhere, so for large $k$ we have $u_l - s_{l,k} < \varepsilon/8$
everywhere, for every $l$. Then $|\varphi_k| \le 2M$, so $\varphi_k \in \mathcal{L}^\infty(\mu)$, and
$|f - \varphi_k| \le \sum_l (u_l - s_{l,k}) \le \varepsilon/2$ everywhere, so $\|f - \varphi_k\|_\infty < \varepsilon$.

## Depends on

- [The space $L^p$ of a measure](../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/lp.md)
- [Measure](../../measures/measures-and-countable-additivity/measures/measure.md)
- [Measurable function](../../measurable-spaces/measurable-spaces-and-measurable-functions/measurable-functions/measurable.md)
- [Indicator function of a set](../../../Algebra/algebraic-identities/indicator-one.md)
- [Lebesgue integral](../../integration/nonnegative-lebesgue-integral/lebesgue-integral/lebesgue-integral.md)

## Proof depends on

- [Countable subadditivity of a measure](../../measures/measures-and-countable-additivity/measures/measure-i-union-le.md)
- [Monotonicity of the integral](../../integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Approximation of nonnegative measurable functions by simple functions](../../integration/approximation-by-simple-functions/exists-monotone-tendsto.md)
- [Continuous maps are Borel measurable](../../measurable-spaces/borel-algebras-and-continuous-maps/continuous-maps-are-borel-measurable/borel-measurable.md)
- [Dominated convergence theorem for nonnegative functions](../../integration/dominated-convergence-theorem/tendsto-lintegral-of-dominated-convergence.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Exercise 17 in Section 7A (version read: the open-access PDF dated 12 June 2026).
