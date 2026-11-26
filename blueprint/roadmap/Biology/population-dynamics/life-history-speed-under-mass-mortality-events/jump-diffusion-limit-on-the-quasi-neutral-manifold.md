# Jump-diffusion limit on the quasi-neutral manifold

**Deterministic model.** Biomasses $X_1,X_2$ of two types and a resource $R$ follow
$$\dot X_i=X_i\big(\beta_iF(R)-\mu_i\big),\qquad \dot R=\gamma G(R)-F(R)\,\boldsymbol\beta\cdot\mathbf X,$$
with Holling type II uptake $F(R)=R/(a+R)$ and renewal $G(R)=R_{\max}-R$. With $\hat{\mathbf X}=\gamma^{-1}\mathbf X$ and $\gamma$ large, $R$ relaxes to the root $R^*(\mathcal E)$ of $G(R)=F(R)\mathcal E$, $\mathcal E=\boldsymbol\beta\cdot\hat{\mathbf X}$, and $\dot{\hat X}_i=\hat X_i(\beta_iF\circ R^*(\boldsymbol\beta\cdot\hat{\mathbf X})-\mu_i)$. Write $\nu_i=\beta_i/\mu_i$ (intrinsic lifetime reproductive success).

**Theorem 1 (competitive exclusion).** If $\nu_1>\nu_2$ and $\hat{\mathbf X}(0)\in\mathbb R^2_{>0}$, then $\hat{\mathbf X}(t)\to\mathbf 0$ when $\nu_1<1/F(R_{\max})$, and $\hat{\mathbf X}(t)\to(\mathcal E_{(1,0)}/\beta_1,0)$ with $\mathcal E_{(1,0)}=(F\circ R^*)^{-1}(1/\nu_1)$ when $\nu_1>1/F(R_{\max})$.

**Quasi-neutral case.** If $\nu_1=\nu_2=\nu>1/F(R_{\max})$, every point of the segment $\Gamma=\{\mathbf x\in\mathbb R^2_{\ge0}:\boldsymbol\beta\cdot\mathbf x=\mathcal E_\Gamma\}$, $\mathcal E_\Gamma=(F\circ R^*)^{-1}(1/\nu)$, is an equilibrium. Add demographic stochasticity at carrying-capacity scale $\gamma$ and mass-mortality events at rate $\kappa$ that multiply $(X_1,X_2)$ by a random survival vector $\mathbf U\sim\Upsilon$ on $[0,1]^2$.

**Corollary 8 (frequency process).** In the limit $\gamma\to\infty$ with time accelerated by $\gamma$ (Theorem 6), the process lives on $\Gamma$, and the frequency $W=z_1/(z_1+z_2)$, a bijection $\Phi:\Gamma\to[0,1]$ with $\Phi^{-1}(w)=\frac{\mathcal E_\Gamma}{\beta_1w+\beta_2(1-w)}(w,1-w)$, is a Markov jump-diffusion with generator
$$\mathbf Af(w)=\mu(w)f'(w)+\tfrac{\sigma(w)^2}{2}f''(w)+\kappa\int_{[0,1]^2}\Big[f\big(\Phi\circ\boldsymbol\pi(\mathbf u\odot\Phi^{-1}(w))\big)-f(w)\Big]\Upsilon(d\mathbf u),$$
where $\boldsymbol\pi$ is the deterministic projection of a post-catastrophe state onto $\Gamma$ along the reduced flow and
$$\sigma(w)^2=\frac{2}{\nu\mathcal E_\Gamma}\,\frac{\beta_1\beta_2\,w(1-w)\,(\beta_1w+\beta_2(1-w))^4}{(\beta_1^2w+\beta_2^2(1-w))^2}.$$
The drift $\mu(w)$ is an explicit rational function proportional to $\beta_2-\beta_1$, vanishing in the neutral case $\beta_1=\beta_2$.

## Expansion

Theorem 1 is the resource-ratio rule: type $i$ persists only if resources stay above $R_i^0=F^{-1}(1/\nu_i)$, and $\nu_1>\nu_2$ means $R_1^0<R_2^0$. In the quasi-neutral case the generator splits into a fast part of order $\gamma^2$ (resource relaxation), a part of order $\gamma$ (deterministic attraction to $\Gamma$) and an order-one part (noise along $\Gamma$ and jumps). The projection $\boldsymbol\pi$ satisfies $\hat{\mathbf G}^\gamma\pi_i=\hat{\mathbf G}^\gamma_0\pi_i$ (Proposition 14), so the singular terms cancel and the limit is identified in the Meyer–Zheng pseudopath topology, which tolerates the instantaneous return to $\Gamma$ after each catastrophe.

## Sources

- É. Martin, D. Steinsaltz, "Evolution of Fast and Slow Life Histories in Resource-Constrained Populations with Mass-Mortality Events", arXiv preprint (2026), Theorem 1, Theorem 6, Corollary 8 and Proposition 14, <https://doi.org/10.48550/arXiv.2609.14597>.
