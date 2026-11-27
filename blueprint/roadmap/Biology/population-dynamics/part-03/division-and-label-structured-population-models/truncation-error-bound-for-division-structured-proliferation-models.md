# Truncation error bound for division-structured proliferation models

**Setting.** In the division- and label-structured population model the overall label density is an infinite sum over division numbers, $M(t,x)=\sum_{i\ge0}N_i(t,x)$, where the subpopulation sizes $\bar N_i$ solve the ODE chain $\dot{\bar N}_0=-(\alpha_0+\beta_0)\bar N_0$, $\dot{\bar N}_i=-(\alpha_i+\beta_i)\bar N_i+2\alpha_{i-1}\bar N_{i-1}$. For computation one keeps the first $S$ generations,

$$\hat M_S(t,x)=\sum_{i=0}^{S-1}N_i(t,x).$$

On a finite horizon $[0,T]$ suppose the rates are uniformly bounded:

$$\alpha_{\sup}=\sup_{t\le T,\,i}\alpha_i(t),\qquad \alpha_{\inf}=\inf_{t\le T,\,i}\alpha_i(t)\ge0,\qquad \beta_{\inf}=\inf_{t\le T,\,i}\beta_i(t)>0 .$$

**Theorem (convergence).** Under these bounds the series defining $M(t,x)$ (and the total population size $\sum_i\bar N_i$) converges for every finite $T$.

**Theorem (truncation error).** For every truncation index $S$,

$$\frac{\|M(T,\cdot)-\hat M_S(T,\cdot)\|_{L^1}}{\|M(0,\cdot)\|_{L^1}}\le E_S(T)=\Big(e^{2\alpha_{\sup}T}-\sum_{i=0}^{S-1}\frac{(2\alpha_{\sup}T)^i}{i!}\Big)e^{-(\alpha_{\inf}+\beta_{\inf})T}.$$

**Corollary.** The relative truncation error is at most $\epsilon$ whenever $S$ is chosen with $E_S(T)\le\epsilon$. Since $E_S(T)=e^{(2\alpha_{\sup}-\alpha_{\inf}-\beta_{\inf})T}\,\mathbb{P}\big(\mathrm{Poisson}(2\alpha_{\sup}T)\ge S\big)$, the required number of generations is governed by the Poisson mean $2\alpha_{\sup}T$, so a small ODE system suffices over typical assay horizons.

The error is relative to the initial cell number, which is natural because the system is linear: the bound does not depend on $\|M(0,\cdot)\|_{L^1}$.

## Expansion

Because $n_i(t,\cdot)$ are probability densities, $\|N_i(T,\cdot)\|_{L^1}=\bar N_i(T)$, so the error is the tail $\sum_{i\ge S}\bar N_i(T)$. Compare the ODE chain with a bounding system in which every division inflow uses $\alpha_{\sup}$ and every outflow uses $\alpha_{\inf}+\beta_{\inf}$. By positivity of the lower-triangular system, its solution dominates $\bar N_i$ componentwise, and it has the closed form $\bar B_i(t)=\frac{(2\alpha_{\sup}t)^i}{i!}e^{-(\alpha_{\inf}+\beta_{\inf})t}\bar N_{0,\mathrm{init}}$, generalizing the constant-rate solution. Summing its tail from $i=S$ gives $E_S(T)$, and summing all terms gives the finite bound $e^{(2\alpha_{\sup}-\alpha_{\inf}-\beta_{\inf})T}\bar N_{0,\mathrm{init}}$ that proves convergence.

## Depends on

- [Decomposition of the division- and label-structured population model](decomposition-of-the-division-and-label-structured-population-model.md)

## Sources

- J. Hasenauer, D. Schittler, F. Allgöwer, "A computational model for proliferation dynamics of division- and label-structured populations", arXiv:1202.4923 (2012): Theorem 2 (convergence), Theorem 3 (truncation error bound), Corollary 3 (choice of truncation index), Section 3.3 and the appendix proofs. <https://doi.org/10.48550/arXiv.1202.4923>. Published version: Jan Hasenauer, Daniella Schittler, Frank Allgöwer, "Analysis and simulation of division- and label-structured population models", Bulletin of Mathematical Biology 74(11) (2012), 2692–2732, <https://doi.org/10.1007/s11538-012-9774-5>; locators above refer to the arXiv version.
