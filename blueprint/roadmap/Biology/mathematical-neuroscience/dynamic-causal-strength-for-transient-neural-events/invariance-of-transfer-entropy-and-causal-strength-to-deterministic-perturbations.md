# Invariance of transfer entropy and causal strength to deterministic perturbations

**Time-inhomogeneous SVAR model.** Two signals (e.g. two brain regions) follow

$$X^1_t=a_t^{\top}X^1_{p,t}+b_t^{\top}X^2_{p,t}+\eta^1_t,\qquad X^2_t=c_t^{\top}X^1_{p,t}+d_t^{\top}X^2_{p,t}+\eta^2_t,$$

with $X^k_{p,t}=(X^k_{t-1},\dots,X^k_{t-p})^{\top}$ and independent Gaussian innovations $\eta^k_t\sim N(k^k_t,\sigma^2_{k,t})$ whose means and variances, like the coefficients, may vary with peri-event time $t$; peri-event trials are i.i.d. samples of this process.

**Measures.** Time-varying transfer entropy is

$$\mathrm{TE}_{X^2\to X^1}(t)=\mathbb E\Big[\log\frac{p(X^1_t\mid X^1_{p,t},X^2_{p,t})}{p(X^1_t\mid X^1_{p,t})}\Big].$$

Dynamic causal strength (DCS) compares the mechanism with the post-intervention world in which the arrow $X^2_{p,t}\to X^1_t$ is cut by feeding an independent copy of $X^2_{p,t}$:

$$p_{\mathrm{DCS}}(X^1_t\mid X^1_{p,t})=\int p(X^1_t\mid X^1_{p,t},X^2_{p,t})\,p(X^2_{p,t})\,dX^2_{p,t},\qquad \mathrm{DCS}_{X^2\to X^1}(t)=\mathbb E\,D_{KL}\big(p(X^1_t\mid X^1_{p,t},X^2_{p,t})\,\|\,p_{\mathrm{DCS}}(X^1_t\mid X^1_{p,t})\big).$$

Relative DCS (rDCS) instead feeds an independent copy of the cause at a baseline reference time $t_{\mathrm{ref}}$, replacing $p(X^2_{p,t})$ by $p(X^2_{p,t_{\mathrm{ref}}})$ in the mixture.

**Proposition 1.** In the linear SVAR model, TE and DCS are invariant to deterministic perturbations, i.e. to arbitrary changes of the innovation means $(k^1_t,k^2_t)$ at any times. rDCS is not invariant in general.

Consequently, a transient trial-locked drive of the cause region (for instance increasingly strong stimulation) leaves TE and DCS unchanged and, as the innovation variance shrinks, they can be made arbitrarily small despite a large effect on the mean of the target, whereas rDCS registers the induced change; in a stationary system DCS and rDCS coincide.

## Expansion

Shifting one innovation mean by $\alpha$ at time $t_0$ changes the process by the deterministic solution $(U,V)$ of $U_t=a^{\top}U_{p,t}+b^{\top}V_{p,t}$, $V_t=c^{\top}U_{p,t}+d^{\top}V_{p,t}+\alpha\,\delta_{t,t_0}$, which is zero before $t_0$. So the perturbed joint density of $(X^1_t,X^1_{p,t},X^2_{p,t})$ is the original density translated by $(U_t,U_{p,t},V_{p,t})$, and so are all its conditionals and the cut-arrow mixture; a change of variables removes the translation from every log-ratio, giving invariance of TE and DCS, and general perturbations follow by linearity. The rDCS reference mixture uses the cause distribution at $t_{\mathrm{ref}}$, before the perturbation, so the translation does not cancel. TE has a further defect for strongly synchronised signals: as the effect becomes predictable from its own past, TE vanishes even though the coupling is unchanged, while DCS stays positive. For spontaneous events, trials must be aligned on the putative cause: selecting and aligning on threshold crossings of the effect biases the measures and can even reverse the inferred direction.

## Sources

- Shao K, Logothetis NK, Besserve M, "Information theoretic measures of causal influences during transient neural events" (2023), SVAR model (2a)-(2b), the definitions of TE, DCS and rDCS (Sections 2.2-2.4), Proposition 1 with its proof, and Section 2.5 on alignment, <https://doi.org/10.3389/fnetp.2023.1085347>, PMCID PMC10266490.
