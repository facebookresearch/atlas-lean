# Control reproduction number with endogenous bed-net coverage

**Model.** Host 1 ($S_{h1},I_{h1},R_{h1}$, total $N_{h1}$, SIRS) can use insecticide-treated nets with coverage $\theta\in[0,1]$; host 2 ($S_{h2},I_{h2}$, total $N_{h2}$, SIS) cannot. Vectors $S_v,I_v$ grow logistically. With biting rate $c(\theta)$, vector preference weight $\alpha_v(\theta)$ for host 1 and transmission probabilities $\beta_{hv}$ (vector to host) and $\beta_{vh}$ (host to vector),

$$\dot I_{h1}=\frac{\alpha_v(\theta)c(\theta)\beta_{hv}I_vS_{h1}}{\alpha_v(\theta)N_{h1}+N_{h2}}-(\mu_1+d_1)I_{h1},\qquad \dot I_{h2}=\frac{c(\theta)\beta_{hv}I_vS_{h2}}{\alpha_v(\theta)N_{h1}+N_{h2}}-(\mu_2+d_2)I_{h2},$$

$$\dot I_v=\frac{c(\theta)\beta_{vh}(\alpha_v(\theta)I_{h1}+I_{h2})S_v}{\alpha_v(\theta)N_{h1}+N_{h2}}-d_3(\theta)I_v,\qquad \dot S_v+\dot I_v=(b_3(\theta)-b_{31}N_v)N_v-d_3(\theta)N_v,$$

$$\dot\theta=p\,\theta(1-\theta)\big(C_1I_{h1}+C_2(S_v+I_v)-m\big),$$

where recovery rates are $\mu_i$, host turnover $d_i$, and $m$ is the net cost of using a net. The region with $N_{h1},N_{h2}$ fixed, $0\le S_v+I_v\le K(0)$ and $\theta\in[0,1]$ is positively invariant.

**Reproduction numbers.** At a disease-free state with vector carrying capacity $K(\theta^*)$ and coverage $\theta^*$, the next-generation matrix gives the control reproduction number

$$R_c(\theta^*)=\frac{\beta_{hv}\beta_{vh}\,c(\theta^*)^2K(\theta^*)}{\big(\alpha_v(\theta^*)N_{h1}+N_{h2}\big)^2d_3(\theta^*)}\left(\frac{\alpha_v(\theta^*)^2N_{h1}}{\mu_1+d_1}+\frac{N_{h2}}{\mu_2+d_2}\right),$$

and $R_0=R_c(0)$ is the reproduction number without nets.

**Equilibria.** The vector-free states with $\theta\in\{0,1\}$ are unstable. The disease-free states $(0,0,0,0,K(0),0)$ and $(0,0,0,0,K(\theta^*),\theta^*)$, $\theta^*\in(0,1]$, are locally asymptotically stable when $R_0<1$, respectively $R_c(\theta^*)<1$. Endemic equilibria with $\theta=0$, $\theta=1$ and interior $\theta^*$ exist when $R_0>1$, $R_c(1)>1$, and $R_c(\theta^*)>1$ with a sign change of the coverage-balance function, respectively; the interior equilibrium can undergo saddle-node and Hopf bifurcations, giving sustained oscillations of prevalence and coverage.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Each infected host of type $i$ is bitten at a rate proportional to its preference weight divided by the total weighted host population, so the host-to-vector and vector-to-host generation factors are $c\beta_{vh}K\alpha_v^{(i)}/((\alpha_vN_{h1}+N_{h2})(\mu_i+d_i))$ and $c\beta_{hv}\alpha_v^{(i)}N_{hi}/((\alpha_vN_{h1}+N_{h2})d_3)$; summing over host types gives the product form, which is $R_c$ (not its square root) in this convention. Nets lower $c$ and $K$ and raise $d_3$, but by lowering $\alpha_v$ they also divert bites to host 2, so $R_c(\theta)$ need not decrease monotonically in $\theta$. The replicator equation for $\theta$ has interior rest points where the perceived benefit $C_1I_{h1}+C_2N_v$ equals the cost $m$, which couples behaviour to prevalence.

## Sources

- S. Shetgaonkar, A. Sharma, "Nonlinear Feedbacks Between Host Behavior and Vector Adaptation in a Multi-Host Vector-Borne Disease Model", arXiv:2606.31768 (2026), model (eqn1), Proposition 1, Theorems 2–6, Appendix (next-generation matrix), <https://doi.org/10.48550/arXiv.2606.31768>.
