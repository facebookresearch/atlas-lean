# Fold normal form and the singular Andronov–Hopf canard values

**Setting.** Consider a planar slow–fast system $w' = \varepsilon g(w,v,\varepsilon,\lambda)$, $v' = f(w,v,\varepsilon,I)$ with $0 < \varepsilon \ll 1$, input current $I$ and parameter $\lambda$. Assume: (1) the critical manifold $S = \{f(w,v,0,I) = 0\}$ is a cubic-shaped graph $w = \varphi_I(v)$ with attracting outer branches $S_a^\pm$, a repelling middle branch $S_r$, and regular folds $F^\pm$, and $\partial f/\partial w < 0$ on $S$; (2) the $w$-nullcline $g = 0$ is the graph of an increasing function of $v$; (3) all equilibria lie on $S_r$ or $S_a^-$ (one, two or three of them).

**Proposition (normal form at the lower fold).** Under these assumptions the family can be transformed near $F^-$ into

$$x' = \varepsilon\big(c\,y - \sigma x - a + O(x^2, y^3, xy, \varepsilon y^2)\big), \qquad y' = y^2 - x + \beta y^3 + O(y^4),$$

with $\sigma = \pm 1$, $\sigma c \ge 0$ and $\beta \ne 0$, where $a$, $c$, $\beta$ are explicit functions of $(I,\lambda,\varepsilon)$. For $a < 0$ there is a stable equilibrium on $S_a^-$; for $a > 0$ there is none and $F^-$ is a jump point. The fold is a singular Andronov–Hopf point when $a = 0$, $c > 0$, and a singular Bogdanov–Takens point when $a = c = 0$. Neglecting the higher-order terms, a cusp of equilibria occurs at

$$a_{\mathrm{cusp}} = \frac{\sigma}{27\beta^2}, \qquad c_{\mathrm{cusp}} = -\frac{\sigma}{3\beta}.$$

**Theorem (singular Andronov–Hopf bifurcation and canards).** Suppose the fold undergoes a singular Andronov–Hopf bifurcation at $I = I_{\mathrm{bif}}$ ($a = 0$, $c > 0$, $\partial a/\partial I \ne 0$). Then for $0 < \varepsilon \ll 1$ there is an Andronov–Hopf bifurcation at $I_h = I_{\mathrm{bif}} + H_1\varepsilon + O(\varepsilon^{3/2})$ and a canard explosion at $I_c = I_{\mathrm{bif}} + (H_1 + K_1)\varepsilon + O(\varepsilon^{3/2})$, within an exponentially small parameter interval. In the normal form, for $c > 0$ sufficiently large, $a_h = H_1^a\varepsilon + O(\varepsilon^{3/2})$ and $a_c = (H_1^a + K_1^a)\varepsilon + O(\varepsilon^{3/2})$ with

$$H_1^a = \frac{\sigma c}{2}, \qquad K_1^a = -\frac{c}{4}\Big(\sigma + \frac{3}{2}\beta c\Big);$$

the bifurcation is supercritical if $K_1^a > 0$ and subcritical if $K_1^a < 0$. Criticality changes at $c_{\mathrm{bautin}} = -2\sigma/(3\beta)$, where for $0 < \varepsilon \ll 1$ a codimension-two Bautin point occurs; for $0 < c < c_{\mathrm{bautin}}$ the subcritical Hopf branch is accompanied by a saddle-node of canard cycles exponentially close to $a_c$.

## Depends on

- [Statement of the local Hopf bifurcation theorem on ℝᴺ](../../../systems-biology/three-variable-repressilator/hopf-bifurcation-theorem.md)

## Expansion

The proof straightens the $v$-nullcline by dividing by a positive factor of $f$, translates the fold to the origin, and uses near-identity changes of variables to remove the $y^2$ term from the slow equation, then rescales so that the coefficient of $x$ is $\pm 1$. The equilibrium near the fold sits at $y \approx \varepsilon H_1^a/c$ and the trace of the linearization is $-\sigma + 2H_1^a/c + O(\varepsilon^2)$, which vanishes at $H_1^a = \sigma c/2$. The canard value is where the slow manifold admits a smooth expansion $x = \varphi_0(y) + \varepsilon\varphi_1(y) + \varepsilon^2\varphi_2(y) + \cdots$ through the fold; requiring $\varphi_2$ to have no pole at $y = 0$ fixes $K_1^a$, which doubles as the first Lyapunov coefficient. The cusp values come from a triple root of the equilibrium equation $\sigma(y^2 + \beta y^3) - c y + a = 0$. In the canonical neuron model of the paper, $\sigma = 1$, $\beta = -1/d^2$ and $c_{\mathrm{bautin}} = 2d^2/3$.

## Sources

- P. De Maesschalck, M. Wechselberger, "Neural excitability and singular bifurcations", Journal of Mathematical Neuroscience 5:16 (2015), Assumptions 1–5, Proposition 1 (Eq 15), Eqs (16)–(17), Theorem 1 (Eqs 21–23), Eq (24) and Lemmas 1–2, <https://doi.org/10.1186/s13408-015-0029-2>, PMCID PMC4526515.
