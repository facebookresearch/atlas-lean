# Yamada–Watanabe pathwise uniqueness for Hölder-type diffusion coefficients

Let $b:\mathbb R\to\mathbb R$ be Lipschitz and let $\sigma:\mathbb R\to\mathbb R$ satisfy

$$|\sigma(x)-\sigma(y)|\le h(|x-y|)\qquad(x,y\in\mathbb R),$$

where $h$ is continuous and strictly increasing with $h(0)=0$ and $\int_0^\varepsilon h(u)^{-2}\,du=\infty$ for every $\varepsilon>0$. Then pathwise uniqueness holds for $dX_t=b(X_t)\,dt+\sigma(X_t)\,dB_t$: if $X$ and $Y$ are [weak solutions](gluing-two-weak-solutions-over-a-common-initial.md) on the same filtered probability space with the same Brownian motion and $X_0=Y_0$ almost surely, then $X$ and $Y$ are indistinguishable.

The condition covers $h(u)=C\sqrt u$. In particular it covers the Wright–Fisher coefficient $\sigma(x)=\sqrt{x(1-x)}$ on $[0,1]$, extended by $0$ outside $[0,1]$: on $[0,1]$ it is [$\frac12$-Hölder with constant $1$](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/abs-sqrt-mul-one-sub-sub-le.md), and for $x\in[0,1]$, $y<0$ one has $\sqrt{x(1-x)}\le\sqrt x\le\sqrt{x-y}$, symmetrically for $y>1$. It also covers Feller's coefficient $\sqrt{\gamma x^+}$ with $h(u)=\sqrt{\gamma u}$.

## Depends on

- [Yamada–Watanabe approximating functions](yamada-watanabe-approximating-functions-determin.md)
- [Gluing two weak solutions over a common initial value and Brownian motion](gluing-two-weak-solutions-over-a-common-initial.md)

## Proof depends on

- [Ito formula for Ito processes (time-dependent, localized)](../it-s-formula/ito-formula-for-ito-processes-time-dependent-loc.md)
- [Strong solutions of SDEs with Lipschitz coefficients](../sde-lipschitz-exists-unique.md)
- [Gronwall inequality in integral form](../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Expansion

A full proof applies Itô's formula to $\varphi_n(X_t-Y_t)$ with the [approximating functions](yamada-watanabe-approximating-functions-determin.md), localized at exit times of compacts. The second-order term is at most $\frac12\mathbb E\int_0^t\varphi_n''(X_s-Y_s)\,h(|X_s-Y_s|)^2\,ds\le t/n$; the stochastic integral has mean zero after localization; and the drift term is at most $L\int_0^t\mathbb E|X_s-Y_s|\,ds$. Letting $n\to\infty$ and applying the [Gronwall inequality](../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md) to $u(t)=\mathbb E|X_{t\wedge\tau}-Y_{t\wedge\tau}|$ gives $X=Y$ up to each localizing time, and continuity of paths gives indistinguishability.

## Sources

- T. Yamada and S. Watanabe, *On the uniqueness of solutions of stochastic differential equations*, J. Math. Kyoto Univ. 11 (1971), 155–167, uniqueness theorem.
- Wikipedia contributors, *Yamada–Watanabe theorem*, <https://en.wikipedia.org/wiki/Yamada%E2%80%93Watanabe_theorem>, statement summary (background).
