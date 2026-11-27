# Fixation probability under weak frequency-dependent selection

**Setting.** Let $\sigma : [0,1] \to \mathbb R_+$ be continuously differentiable and $\psi : [0,1] \to \mathbb R$ such that $\mu := \psi\,\sigma^2$ is bounded. For $\alpha \in \mathbb R$ let $X$ solve

$$dX = \alpha\,\mu(X)\,dt + \sigma(X)\,dW, \qquad X_0 = x \in (0,1),$$

up to $T = T_0 \wedge T_1$, the first hitting time of $\{0,1\}$. The main case is the Wright–Fisher diffusion with frequency-dependent selection, $\sigma^2(y) = y(1-y)$, where $\alpha\psi(y)$ is the fitness advantage of the focal type at frequency $y$.

**Theorem (Theorem 1).** As $\alpha \to 0$,

$$\frac{1}{2\alpha}\Big(\mathbf P^\alpha_x(T_1 < T_0) - x\Big) \longrightarrow x\int_0^1 (1-y)\,\psi(y)\,dy - \int_0^x (x-y)\,\psi(y)\,dy.$$

The limit does not depend on $\sigma$. For monomials (Corollary 2.1), $\psi(x) = x^k$ gives $\partial_\alpha \mathbf P^\alpha_x(T_1 < T_0)|_{\alpha=0} = \binom{k+2}{2}^{-1} x(1-x^{k+1})$, and $\psi(x) = (1-x)^k$ gives $\binom{k+2}{2}^{-1}(1-x)\big(1-(1-x)^{k+1}\big)$.

**Corollary (generalized one-third rule).** For linear frequency dependence $\psi(y) = \beta - \gamma y$,

$$\mathbf P^\alpha_x(X_T = 1) = x + \alpha\,x(1-x)\Big(\beta - \frac{\gamma}{3}(1+x)\Big) + O(\alpha^2),$$

so for small $\alpha > 0$ and fixed initial frequency $x$, selection raises the fixation probability above its neutral value $x$ if and only if $\psi\big(\frac{1+x}{3}\big) > 0$. As $x \to 0$ this is the [one-third rule](../../../moran-model/one-third-rule-under-weak-selection.md) $\psi(1/3) > 0$.

## Depends on

- [The one-third rule for weak selection in the Moran process](../../../moran-model/one-third-rule-under-weak-selection.md)

## Expansion

The fixation probability is $P_x = S(x)/S(1)$ with scale function $S(x) = \int_0^x \exp\!\big(-2\alpha\int_0^y \psi(z)\,dz\big)\,dy$, because $\mu/\sigma^2 = \psi$; the volatility cancels from the scale density, which is why the first-order term is independent of $\sigma$. Expanding the exponential to first order in $\alpha$ gives $S(x) \approx x - 2\alpha\int_0^x (x-y)\psi(y)\,dy$, and the quotient produces the stated limit. For linear $\psi$, both integrals are polynomials, and the sign of the correction is the sign of $\psi$ at the point $(1+x)/3$.

## Sources

- Peter Pfaffelhuber and Anton Wakolbinger, "Fixation probabilities and hitting times for low levels of frequency-dependent selection", *Theor. Popul. Biol.* 124 (2018), 61-69. <https://doi.org/10.1016/j.tpb.2018.09.003>
- Preprint version (the locators in this item follow its numbering): Peter Pfaffelhuber and Anton Wakolbinger, "Fixation probabilities and hitting times for low levels of frequency-dependent selection", arXiv:1801.01584 (2018), Section 1 (equations for the linear case), Section 2, Theorem 1, Corollary 2.1, <https://doi.org/10.48550/arXiv.1801.01584>.
