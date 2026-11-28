# Healthy-state stability and endemic equilibria of networked SEIRS with travel flows

**Setting.** $n$ sub-populations of constant sizes $N_i$ are connected by travel: a fraction $\gamma_j$ of node $j$ leaves per unit time and a share $w_{ij}$ of those travelers arrives at node $i$, with total inflow equal to total outflow at every node (Assumption 1). Local SEIRS dynamics with infection, incubation, recovery and immunity-loss rates $\beta_i, \sigma_i, \delta_i, \alpha_i > 0$ give, for the proportions $(s_i,e_i,x_i,r_i)$,

$$\dot s_i = \alpha_ir_i - (\beta_ix_i + \gamma_i)s_i + \sum_{j\ne i}\frac{N_j}{N_i}w_{ij}\gamma_js_j, \qquad \dot e_i = \beta_ix_is_i - (\sigma_i + \gamma_i)e_i + \sum_{j\ne i}\frac{N_j}{N_i}w_{ij}\gamma_je_j,$$

$$\dot x_i = \sigma_ie_i - (\delta_i + \gamma_i)x_i + \sum_{j\ne i}\frac{N_j}{N_i}w_{ij}\gamma_jx_j, \qquad \dot r_i = \delta_ix_i - (\alpha_i + \gamma_i)r_i + \sum_{j\ne i}\frac{N_j}{N_i}w_{ij}\gamma_jr_j.$$

With $B = \operatorname{diag}(\beta_i)$, $\Sigma = \operatorname{diag}(\sigma_i)$, $D = \operatorname{diag}(\delta_i)$, $\Gamma = \operatorname{diag}(\gamma_i)$ and the flow matrix $\Phi = N^{-1}W\Gamma N$, let

$$U = \begin{bmatrix} -\Sigma - \Gamma + \Phi & B \\ \Sigma & -D - \Gamma + \Phi \end{bmatrix}.$$

**Theorem.** Under Assumptions 1–2 (positive rates, initial proportions summing to one):
1. (Lemma 5, Proposition 2) Proportions stay in $[0,1]$ and sum to one at every node, and the healthy state $(\mathbf 1, \mathbf 0, \mathbf 0, \mathbf 0)$ is always an equilibrium.
2. (Proposition 3, Corollary 1) If the spectral abscissa $s(U) < 0$, the healthy state is locally exponentially stable; if $s(U) > 0$, it is unstable.
3. (Theorem 1) If the Jacobian at the healthy state has distinct eigenvalues, no permissible perturbation of the travel rates $\gamma_i$ (keeping inflow equal to outflow) changes the local stability of the healthy state.
4. (Theorems 2–3) If $\inf_{t \ge t_0} s\big(-Q(t) + M(t)\big) > 0$ for the matrices of the stacked linear-in-state form of the system, an endemic equilibrium with all components positive exists; if moreover $\beta_i \ge \gamma_i$ for every $i$, it is unique.

## Expansion

At the healthy state the Jacobian is block lower triangular: the recovered block $-A - \Gamma + \Phi$ is stable by Gershgorin's theorem because $\gamma_i = \sum_{j\ne i}\phi_{ij}$, so stability is decided by the exposed–infected block $U$, a Metzler matrix whose spectral abscissa has the sign of $\rho(-\Lambda^{-1}N) - 1$ for its diagonal–off-diagonal splitting (Proposition 1), i.e. a network reproduction number. Intuitively, travel only moves individuals between nodes without changing their epidemiological state, consistent with the fact that flows that conserve node sizes cannot by themselves move the system across the stability threshold when the spectrum is simple. The model is used to evaluate travel restrictions and to estimate how infections move between counties (the paper's case study uses Minnesota COVID-19 data).

## Sources

- Brooks A. Butler, Raphael Stern and Philip E. Paré, "Analysis and applications of population flows in a networked SEIRS epidemic process", arXiv:2309.11588 (2023), Section 3 (model, Assumptions 1–2, Lemma 5), Section 4 (Propositions 1–3, Corollary 1, Theorems 1–3), <https://doi.org/10.48550/arXiv.2309.11588>. Published version: IEEE Transactions on Network Science and Engineering 11 (2024) 6664–6677, <https://doi.org/10.1109/tnse.2024.3468991>.
