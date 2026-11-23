# The dual of $L^1$ is $L^\infty$ for a σ-finite measure

Let $(X, \mathcal{M}, \mu)$ be a measure space with $\mu$ σ-finite, and let the scalar field $\mathbb{F}$ be
$\mathbb{R}$ or $\mathbb{C}$ throughout. For $h \in L^\infty(\mu)$ and $f \in L^1(\mu)$, the product $fh$ is integrable,
and $\varphi_h \colon L^1(\mu) \to \mathbb{F}$ is defined by

$$\varphi_h(f) = \int f h \, d\mu.$$

Then each $\varphi_h$ is a bounded linear functional on $L^1(\mu)$ with $\|\varphi_h\| = \|h\|_\infty$, and the map
$h \mapsto \varphi_h$ is a linear bijection from $L^\infty(\mu)$ onto the dual space $(L^1(\mu))'$ of bounded linear
functionals on $L^1(\mu)$; it is therefore an isometric isomorphism.

## Proof

Let $h \in L^\infty(\mu)$. For $f \in L^1(\mu)$, Hölder's inequality gives $\|fh\|_1 \le \|f\|_1 \|h\|_\infty$, so $fh$
is integrable and, by the bound on the norm of an integral,
$|\varphi_h(f)| \le \int |fh| \, d\mu \le \|h\|_\infty \|f\|_1$. Linearity of the integral makes $\varphi_h$ and
$h \mapsto \varphi_h$ linear, and $\|\varphi_h\| \le \|h\|_\infty$. If $0 < \varepsilon < \|h\|_\infty$, the set
$\{|h| > \|h\|_\infty - \varepsilon\}$ has positive measure, so by σ-finiteness it contains a measurable set $E$ with
$0 < \mu(E) < \infty$. The function $f$ equal to $\overline{h}/|h|$ on $E$, where $|h| > 0$, and to $0$ elsewhere has
$\|f\|_1 = \mu(E)$ and, by monotonicity of the integral,
$\varphi_h(f) = \int_E |h| \, d\mu \ge (\|h\|_\infty - \varepsilon) \mu(E)$. Hence $\|\varphi_h\| = \|h\|_\infty$, and
$h \mapsto \varphi_h$ is injective.

For surjectivity, let $\varphi \in (L^1(\mu))'$, and suppose first that $\mu(X) < \infty$. Put
$\nu(E) = \varphi(\chi_E)$ for $E \in \mathcal{M}$. If $E$ is the union of disjoint $E_1, E_2, \ldots \in \mathcal{M}$,
then $\|\chi_E - \sum_{k \le n} \chi_{E_k}\|_1 = \mu\big(\bigcup_{k > n} E_k\big) = \sum_{k > n} \mu(E_k) \to 0$ by
countable additivity, so $\nu(E) = \sum_k \nu(E_k)$ by continuity and linearity of $\varphi$. Thus the real and
imaginary parts of $\nu$ are signed measures with real values, and $|\nu(E)| \le \|\varphi\| \mu(E)$, so they vanish on
the sets of measure $0$. The Radon–Nikodym theorem, applied to them, gives an integrable $h$ with
$\nu(E) = \int_E h \, d\mu$ for every $E \in \mathcal{M}$, and by linearity $\varphi(g) = \int g h \, d\mu$ for every
simple function $g$. Then $|h| \le \|\varphi\|$ almost everywhere. Otherwise, cover
$\{w \in \mathbb{F} : |w| > \|\varphi\|\}$ by countably many closed discs $D$, of centre $z$ and radius $r$ with
$|z| - r > \|\varphi\|$; by countable subadditivity, one $E = h^{-1}(D)$ has $\mu(E) > 0$, and then, as the constant $z$
has integral $z \mu(E)$ over $E$, for the measure $\mu$ restricted to $E$,
$|\int_E h \, d\mu - z \mu(E)| = |\int_E (h - z) \, d\mu| \le \int_E |h - z| \, d\mu \le r \mu(E)$ gives
$|\varphi(\chi_E)| \ge (|z| - r) \mu(E) > \|\varphi\| \mu(E)$, which is impossible. So $h \in L^\infty(\mu)$, and the
bounded functionals $\varphi$ and $\varphi_h$ agree on the simple functions, which are dense in $L^1(\mu)$; hence
$\varphi = \varphi_h$.

In general, let $X_1, X_2, \ldots \in \mathcal{M}$ be disjoint, with finite measures and union $X$. The finite case,
applied on each $X_n$ to $\varphi$ restricted to the functions in $L^1(\mu)$ that vanish outside $X_n$, gives $h_n$ on
$X_n$ with $|h_n| \le \|\varphi\|$ almost everywhere and $\varphi(g) = \int g h_n \, d\mu$ for those $g$. Let $h = h_n$
on each $X_n$. Then $|h| \le \|\varphi\|$ almost everywhere, by countable subadditivity, and by linearity
$\varphi(\chi_E) = \int_E h \, d\mu$ whenever $E \in \mathcal{M}$ lies in $Y_n = X_1 \cup \cdots \cup X_n$ for some $n$.
For $E \in \mathcal{M}$ with $\mu(E) < \infty$, continuity of measures from above gives $\mu(E \setminus Y_n) \to 0$, so
$\chi_{E \cap Y_n} \to \chi_E$ in $L^1(\mu)$, while Hölder's inequality gives
$|\int_{E \setminus Y_n} h \, d\mu| \le \|h\|_\infty \mu(E \setminus Y_n) \to 0$; hence
$\varphi(\chi_E) = \int_E h \, d\mu$. So $\varphi$ and $\varphi_h$ agree on the simple functions whose nonzero values
are taken on sets of finite measure, which are dense in $L^1(\mu)$, and $\varphi = \varphi_h$.

## Depends on

- [The space $L^p$ of a measure](../../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/lp.md)
- [Measure](../../../measures/measures-and-countable-additivity/measures/measure.md)
- [σ-finite measure](../../../measures/measures-and-countable-additivity/measures/sigma-finite.md)
- [Lebesgue integral](../../../integration/nonnegative-lebesgue-integral/lebesgue-integral/lebesgue-integral.md)
- [Hölder's inequality with an essentially bounded factor](../../h-lder-and-minkowski-inequalities-for-integrals/h-lder-s-inequality/e-lp-norm-le-e-lp-norm-mul-e-lp-norm-top.md)

## Proof depends on

- [Hölder's inequality with an essentially bounded factor](../../h-lder-and-minkowski-inequalities-for-integrals/h-lder-s-inequality/e-lp-norm-le-e-lp-norm-mul-e-lp-norm-top.md)
- [Norm of an integral](../../../integration/nonnegative-lebesgue-integral/lebesgue-integral/norm-integral-le-integral-norm.md)
- [Additivity of the integral of integrable functions](../../../integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-add.md)
- [Homogeneity of the integral](../../../integration/nonnegative-lebesgue-integral/additivity-of-the-integral/integral-smul.md)
- [Monotonicity of the integral](../../../integration/nonnegative-lebesgue-integral/lebesgue-integral/lintegral-mono.md)
- [Countable subadditivity of a measure](../../../measures/measures-and-countable-additivity/measures/measure-i-union-le.md)
- [Continuity of measures from below and from above](../../../measures/measures-and-countable-additivity/continuity-of-measures/measure-continuity.md)
- [Radon–Nikodym theorem for finite signed measures](../../../signed-vector-measures/absolute-continuity-and-decomposition-of-vector/radon-nikodym-theorem-for-signed-measures/with-density-rn-deriv-eq.md)
- [The Radon–Nikodym derivative of a finite signed measure is integrable](../../../signed-vector-measures/absolute-continuity-and-decomposition-of-vector/radon-nikodym-theorem-for-signed-measures/integrable-rn-deriv.md)
- [Simple functions are dense in $L^p$](../../density-of-simple-functions-in-lp/lp-simple-functions-dense.md)
- [Integral of a constant](../../../integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-const.md)
- [Indicator function of a set](../../../../Algebra/algebraic-identities/indicator-one.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 9.42, the case $p = 1$ (version read: the open-access PDF dated 12 June 2026).
