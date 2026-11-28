# Decomposition of the division- and label-structured population model

**Model.** Proliferation assays with a dilutable dye (such as CFSE) record a cell's label concentration $x\ge0$, while its division number $i\in\mathbb{N}_0$ is hidden. The division- and label-structured population (DLSP) model tracks the label density $N_i(t,x)$ of cells that have divided $i$ times:

$$\partial_tN_0+\partial_x\big(\nu(t,x)N_0\big)=-\big(\alpha_0(t)+\beta_0(t)\big)N_0,$$

$$\partial_tN_i+\partial_x\big(\nu(t,x)N_i\big)=-\big(\alpha_i(t)+\beta_i(t)\big)N_i+2\gamma\,\alpha_{i-1}(t)\,N_{i-1}(t,\gamma x),\qquad i\ge1,$$

with $N_0(0,x)=N_{0,\mathrm{init}}(x)$ and $N_i(0,\cdot)\equiv0$ for $i\ge1$. Here $\alpha_i,\beta_i\in C^1$ are division-number-dependent division and death rates (independent of $x$), $\gamma\in(1,2]$ is the label dilution factor at division, and the label decays linearly, $\nu(t,x)=-k(t)x$ (constant or Gompertz $k$). Write $\bar N_i(t)=\int N_i(t,x)\,dx$ for subpopulation sizes and $M(t,x)=\sum_iN_i(t,x)$ for the overall label density.

**Theorem (decomposition).** The solution factors as $N_i(t,x)=\bar N_i(t)\,n_i(t,x)$, where

(i) the sizes solve the linear ODE chain

$$\frac{d\bar N_0}{dt}=-(\alpha_0+\beta_0)\bar N_0,\qquad \frac{d\bar N_i}{dt}=-(\alpha_i+\beta_i)\bar N_i+2\alpha_{i-1}\bar N_{i-1}\ (i\ge1),$$

with $\bar N_0(0)=\bar N_{0,\mathrm{init}}$, $\bar N_i(0)=0$; and

(ii) the normalized label densities solve the decoupled transport equations $\partial_tn_i-k(t)\,\partial_x(xn_i)=0$ with $n_i(0,x)=\gamma^in_{0,\mathrm{init}}(\gamma^ix)$, explicitly

$$N_i(t,x)=\bar N_i(t)\,\gamma^i\,e^{\int_0^tk(\tau)d\tau}\,n_{0,\mathrm{init}}\Big(\gamma^ie^{\int_0^tk(\tau)d\tau}x\Big),\qquad M(t,x)=\sum_{i\ge0}N_i(t,x).$$

Here $n_{0,\mathrm{init}}=N_{0,\mathrm{init}}/\bar N_{0,\mathrm{init}}$, and each $n_i(t,\cdot)$ stays a probability density. (The source's Corollaries 1–2 print the prefactor $e^{-\int_0^tk}$, which neither solves the transport equation nor preserves the integral; its Appendix A has the characteristics used here.) The factorization holds exactly when the label loss rate is linear in $x$.

**Closed forms for the sizes.** If $\alpha_i\equiv\alpha\ge0$ and $\beta_i\equiv\beta>0$, then

$$\bar N_i(t)=\frac{(2\alpha t)^i}{i!}\,e^{-(\alpha+\beta)t}\,\bar N_{0,\mathrm{init}} .$$

If the rates are constant in time with pairwise distinct $\alpha_i+\beta_i$, then $\bar N_0(t)=e^{-(\alpha_0+\beta_0)t}\bar N_{0,\mathrm{init}}$ and, for $i\ge1$,

$$\bar N_i(t)=2^i\Big(\prod_{j=1}^{i}\alpha_{j-1}\Big)\bar N_{0,\mathrm{init}}\sum_{j=0}^{i}\frac{e^{-(\alpha_j+\beta_j)t}}{\prod_{k=0,\,k\ne j}^{i}\big((\alpha_k+\beta_k)-(\alpha_j+\beta_j)\big)} .$$

So a coupled infinite PDE system reduces to a lower-triangular ODE system plus one explicit dilation of the initial label profile per generation.

## Expansion

Integrating the $i$-th PDE in $x$ removes the transport term (it is a divergence) and, after the substitution $x\mapsto\gamma x$, turns $2\gamma\alpha_{i-1}N_{i-1}(t,\gamma x)$ into $2\alpha_{i-1}\bar N_{i-1}$; this is the ODE chain. Substituting $N_i=\bar N_in_i$ back, the reaction terms cancel against $\dot{\bar N}_i$ provided the inflow profile $\gamma n_{i-1}(t,\gamma x)$ coincides with $n_i(t,x)$. This consistency holds when both evolve under the same linear dilation flow $x\mapsto xe^{-\int k}$, which commutes with $x\mapsto\gamma x$, and fails for nonlinear $\nu$. The method of characteristics solves the transport equation. The constant-rate solution is a Poisson-type profile in $i$; the distinct-rate case follows by Laplace transform and partial fractions. Earlier label-structured (single PDE) and division-structured (ODE) proliferation models are recovered as marginals of the DLSP model.

## Sources

- J. Hasenauer, D. Schittler, F. Allgöwer, "A computational model for proliferation dynamics of division- and label-structured populations", arXiv:1202.4923 (2012): model in Section 2, Theorem 1 (decomposition), Corollaries 1–2 (explicit label densities), Lemma 1 and Lemma 2 (subpopulation sizes), Section 4 (relation to label- and division-structured models). <https://doi.org/10.48550/arXiv.1202.4923>. Published version: Jan Hasenauer, Daniella Schittler, Frank Allgöwer, "Analysis and simulation of division- and label-structured population models", Bulletin of Mathematical Biology 74(11) (2012), 2692–2732, <https://doi.org/10.1007/s11538-012-9774-5>; locators above refer to the arXiv version.
