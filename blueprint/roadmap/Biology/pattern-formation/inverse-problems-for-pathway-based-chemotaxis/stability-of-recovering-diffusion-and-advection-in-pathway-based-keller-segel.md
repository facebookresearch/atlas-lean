# Stability of recovering diffusion and advection in the pathway-based Keller–Segel model

**Model.** Cells with an internal adaptation variable $M$ (e.g. average receptor methylation in *E. coli*, or a photoreceptor protein level in phototactic algae) move in a bounded domain $\Omega\subset\mathbb R^2$ according to
$$\partial_t\rho-\nabla\cdot\big(\hat D(M)\nabla\rho\big)+\nabla\cdot\big(\rho\hat K(M)\nabla M\big)=0,\qquad \partial_tM=\gamma\big(\hat\Phi(I)-M\big),\qquad \partial_\nu\rho=0,$$
where $I$ is the external signal and $\hat\Phi(I)$ the adapted internal state. For a static signal, $M(x,t)=\Phi(x)+e^{-\gamma t}(M(x,0)-\Phi(x))$, so the effective coefficients $D(x,t)=\hat D(M)$ and $K(x,t)=\hat K(M)$ (drift $\Gamma=K\nabla\Phi$) relax exponentially, at the same rate $\gamma$, to steady profiles $D_s,K_s$; for $t>t_0\gg1$
$$\hat D(M)=\hat D(\Phi)+e^{-\gamma(t-t_0)}\big[\hat D(M(\cdot,t_0))-\hat D(\Phi)\big]+O(e^{-\gamma(t+t_0)}).$$

**Theorem (conditional Lipschitz stability from internal density data).** Let the coefficients lie in $C^1([0,T];W^{1,\infty}(\Omega))$ with norm at most $A$ and $D\ge\lambda>0$, and write $\rho^i$ for the corresponding densities.

1. (Advection.) If $D$ is known and $\rho^1\ge c_\rho>0$, then for every $t\in[0,T]$
$$\int_\Omega|K^1(t)-K^2(t)|\,|\nabla\Phi|^2\,dx\le\frac{C}{c_\rho}\Big(\|\partial_t\rho^1(t)-\partial_t\rho^2(t)\|_{L^2}+\|\rho^1(t)-\rho^2(t)\|_{H^2}\Big),$$
and on subdomains $\Omega'$ where $|\nabla\Phi|\ge c_\Phi$ this gives an $L^1(\Omega')$ bound with constant $C/(c_\rho c_\Phi^2)$.
2. (Diffusion.) If $K$ is known, then
$$\int_\Omega|D^1(t)-D^2(t)|\,|\nabla\rho^1(t)|^2\,dx\le C\|\rho^1(t)\|_{L^2}\Big(\|\partial_t\rho^1(t)-\partial_t\rho^2(t)\|_{L^2}+\|\rho^1(t)-\rho^2(t)\|_{H^2}\Big).$$
3. (Cross-sensitivity.) If $(D^1,K^1)$ and $(D^2,K^2)$ produce the same density, the diffusion and advection perturbations compensate each other, with explicit weighted estimates quantifying this trade-off.
4. (Relaxation rate.) If $D_s,K_s$ are known, $\rho$ is observed on $(T_*,\infty)$ and the steady-state residual $\mathcal B\rho_s\ne0$ in $H^{-1}(\Omega)$, then the common relaxation rate $\gamma$ is uniquely determined.

## Expansion

Subtracting the two equations, the difference of coefficients appears multiplied by $\nabla\rho^1$ (for $D$) or $\rho^1\nabla\Phi$ (for $K$) in a divergence, while everything else is controlled by $\partial_t(\rho^1-\rho^2)$ and second derivatives of $\rho^1-\rho^2$. Testing against the coefficient difference itself, integrating by parts and using the $H^2$ regularity of solutions gives the weighted $L^1$ bounds; the weights $|\nabla\rho^1|^2$ and $|\nabla\Phi|^2$ show that a coefficient is invisible where the density or signal is flat. The late-time error of the frozen-coefficient model is $O(e^{-\gamma t})$, so the decay rate of $\rho-\rho_s$ along the known steady operator identifies $\gamma$.

## Sources

- Yu'an Li, Lingyun Qiu, Min Tang, Hui Yu, Shenwen Yu, Siqin Zheng, "Recovering the spatiotemporally dependent diffusion and advection coefficients in a pathway-based Keller–Segel model", arXiv:2609.23364 (2026), Propositions 1 and 4, Theorems 1–3, <https://doi.org/10.48550/arXiv.2609.23364>.
