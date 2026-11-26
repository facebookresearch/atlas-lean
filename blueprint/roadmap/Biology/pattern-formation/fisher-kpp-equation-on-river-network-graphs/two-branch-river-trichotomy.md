# Fisher–KPP advection–diffusion on a two-branch river: steady states and trichotomy

**Model.** The upper branch $R_U = (-\infty,0)$ flows into the lower branch $R_L = (0,\infty)$ with constant flow speeds $\beta_U, \beta_L > 0$ and cross-section areas $a_U, a_L > 0$ satisfying conservation of flow $a_L\beta_L = a_U\beta_U$. With unit diffusion and logistic growth,

$$\partial_tw_i - \partial_{xx}w_i + \beta_i\partial_xw_i = w_i - w_i^2 \quad (i = L,U), \qquad w_L(t,0) = w_U(t,0), \qquad a_U\partial_xw_U(t,0) = a_L\partial_xw_L(t,0),$$

(the last line is the Kirchhoff law, equivalent to flux continuity given conservation of flow), with initial data $w_L(0,\cdot) = w_0|_{[0,\infty)}$, $w_U(0,\cdot) = w_0|_{(-\infty,0]}$ for a nonnegative continuous compactly supported $w_0 : \mathbb R \to \mathbb R$, $w_0 \not\equiv 0$ (so the two branches share the trace $w_0(0)$ at the vertex). For these data the problem has a unique nonnegative classical solution.

**Theorem (steady states).** For $\alpha \in (0,1)$, consider the steady-state problem $-\varphi_i'' + \beta_i\varphi_i' = \varphi_i - \varphi_i^2$, $0 < \varphi_i < 1$ ($i = L, U$), $\varphi_L(0) = \varphi_U(0) = \alpha$, $a_U\varphi_U'(0) = a_L\varphi_L'(0)$. Its solutions satisfy:

1. if $0 < \beta_U < 2$ there is none;
2. if $\beta_L, \beta_U \ge 2$ there is exactly one for every $\alpha \in (0,1)$;
3. if $\beta_U \ge 2 > \beta_L$ there is $\alpha_0 \in (0,1)$ such that there is exactly one for $\alpha \in [\alpha_0,1)$ and none for $\alpha < \alpha_0$;
4. every such steady state is increasing in $x$ with $\varphi_U(-\infty) = 0$, $\varphi_L(+\infty) = 1$; as $x \to -\infty$ it decays like $e^{\frac12(\beta_U - \sqrt{\beta_U^2-4})x}$ (like $|x|e^{x}$ if $\beta_U = 2$), except the one with $\alpha = \alpha_0$, which decays at the faster rate $e^{\frac12(\beta_U + \sqrt{\beta_U^2-4})x}$.

**Theorem (long-time trichotomy).** Locally uniformly as $t \to \infty$:

- (persistence at carrying capacity) if $\beta_U < 2$, $(w_L, w_U) \to (1,1)$;
- (washing out) if $\beta_U, \beta_L \ge 2$, $(w_L, w_U) \to (0,0)$, while $\|w_U(t,\cdot)\|_\infty \to 0$ and $\|w_L(t,\cdot)\|_\infty \to 1$: the population is carried downstream rather than wiped out;
- (persistence below carrying capacity) if $\beta_U \ge 2 > \beta_L$, $(w_L,w_U) \to (\varphi_L(\cdot;\alpha_0), \varphi_U(\cdot;\alpha_0))$, the steady state with the fastest decay upstream.

## Depends on

- [Fronts of speed c exist exactly for c at or above the minimal speed](../fisher-kpp-travelling-waves/exists-is-front-iff.md)

## Expansion

The threshold $2$ is the minimal Fisher–KPP front speed $2\sqrt{rD}$ for $u_t = u_{xx} + u - u^2$: in the frame moving with the water, a population spreads upstream iff its intrinsic speed $2$ exceeds the flow speed. Steady states are analyzed in the phase plane of $-\varphi'' + \beta\varphi' = \varphi - \varphi^2$; the linearization at $0$ has characteristic roots $\frac12(\beta \pm \sqrt{\beta^2-4})$, real iff $\beta \ge 2$, so a positive profile tending to $0$ upstream exists only for $\beta_U \ge 2$. Compactly supported data select, by comparison with sub- and supersolutions, the steady state with the fastest upstream decay.

## Sources

- Yihong Du, Bendong Lou, Rui Peng and Maolin Zhou, "The Fisher-KPP equation over simple graphs: varied persistence states in river networks", Journal of Mathematical Biology (2020), <https://doi.org/10.1007/s00285-020-01474-1>. arXiv:1809.06961. Section 1.1, Eqs. (1.4)–(1.10), Theorems 1.1 and 1.2.
