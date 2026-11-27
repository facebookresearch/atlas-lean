# McKean–Vlasov equation for multi-population neural networks

**Network.** Neurons are split into $P$ populations; population $\alpha$ has $N_\alpha$ neurons. Neuron $i$ in population $\alpha = p(i)$ has state $X^{i,N}_t \in \mathbb{R}^d$ (membrane potential, gating or recovery variables, synaptic variables) and obeys

$$dX^{i,N}_t = f_\alpha(t, X^{i,N}_t)\,dt + \sum_{\gamma=1}^P \frac{1}{N_\gamma} \sum_{j:\,p(j) = \gamma} b_{\alpha\gamma}(X^{i,N}_t, X^{j,N}_t)\,dt + g_\alpha(t, X^{i,N}_t)\,dW^i_t + \sum_{\gamma=1}^P \frac{1}{N_\gamma} \sum_{j:\,p(j)=\gamma} \beta_{\alpha\gamma}(X^{i,N}_t, X^{j,N}_t)\,dB^{i\gamma}_t,$$

with independent Brownian motions $W^i$ (intrinsic and external current noise) and $B^{i\gamma}$ (noise on maximal synaptic conductances). With $\bar Z$ an independent copy of $\bar X$ with the same law, the corresponding **mean-field equation** is

$$d\bar X^\alpha_t = f_\alpha(t, \bar X^\alpha_t)\,dt + \sum_{\gamma} \mathbb E_{\bar Z}\big[b_{\alpha\gamma}(\bar X^\alpha_t, \bar Z^\gamma_t)\big]dt + g_\alpha(t, \bar X^\alpha_t)\,dW^\alpha_t + \sum_\gamma \mathbb E_{\bar Z}\big[\beta_{\alpha\gamma}(\bar X^\alpha_t, \bar Z^\gamma_t)\big]dB^{\alpha\gamma}_t, \quad \alpha = 1, \dots, P.$$

If the laws of the $\bar X^\alpha_t$ have densities $p_\alpha(t, z)$, these solve, in the weak sense, the nonlocal McKean–Vlasov–Fokker–Planck system

$$\partial_t p_\alpha = -\operatorname{div}_z\!\Big(\big(f_\alpha(t,z) + \textstyle\sum_\gamma \int b_{\alpha\gamma}(z, y)\, p_\gamma(t, y)\,dy\big)\, p_\alpha\Big) + \tfrac12 \sum_{i,j} \partial^2_{z_i z_j}\big(D^\alpha_{ij}(t, z)\, p_\alpha\big),$$

with $D^\alpha(t, z) = \sum_\gamma \mathbb E_Z[\beta_{\alpha\gamma}(z, Z)]\,\mathbb E_Z[\beta_{\alpha\gamma}(z,Z)]^{\mathsf T} + g_\alpha g_\alpha^{\mathsf T}(t, z)$.

**Local Lipschitz hypotheses are not enough.** Local Lipschitz continuity of $f_\alpha, g_\alpha, b_{\alpha\gamma}, \beta_{\alpha\gamma}$ together with linear growth of $b_{\alpha\gamma}, \beta_{\alpha\gamma}$ and monotone growth of the drift does not make the mean-field equation well posed. With $P = 1$, $f = g = 0$, $\beta = 0$ and $b(x, z) = \phi(z)$ for a bounded, locally Lipschitz $\phi$, it reads $Z_t = Z_0 + \int_0^t \mathbb E\,\phi(Z_s)\,ds$, and for suitable $\phi$ and $Z_0$ this equation has several solutions. The theorem below is therefore stated for the conductance-based models themselves.

**Conductance-based models.** In the FitzHugh–Nagumo and Hodgkin–Huxley networks the state of neuron $i$ is $(V^i, q^i, y^i)$: the membrane potential $V^i$, the recovery variable $q^i = w^i$ (FitzHugh–Nagumo) or the gating variables $q^i = (n^i, m^i, h^i)$ (Hodgkin–Huxley), and the fraction $y^i$ of available neurotransmitter. Synapses are chemical, with reversal potentials $\bar V_{\alpha\gamma}$ and maximal conductances fluctuating around $\bar J_{\alpha\gamma}$ with intensity $\sigma^J_{\alpha\gamma}$:

$$\begin{aligned}
dV^i_t &= F_\alpha(t, V^i_t, q^i_t)\,dt - \sum_\gamma (V^i_t - \bar V_{\alpha\gamma})\,\frac{1}{N_\gamma}\sum_{j:\,p(j)=\gamma} y^j_t\,\big(\bar J_{\alpha\gamma}\,dt + \sigma^J_{\alpha\gamma}\,dB^{i\gamma}_t\big) + \sigma_\alpha\,dW^{i,V}_t,\\
dy^i_t &= \big(a^\alpha_r S_\alpha(V^i_t)(1 - y^i_t) - a^\alpha_d\, y^i_t\big)\,dt + \sqrt{\big|a^\alpha_r S_\alpha(V^i_t)(1 - y^i_t) + a^\alpha_d\, y^i_t\big|}\;\chi(y^i_t)\,dW^{i,y}_t,
\end{aligned}$$

coupled with $dw^i_t = c_\alpha(V^i_t + a_\alpha - b_\alpha w^i_t)\,dt$, or with

$$dx^i_t = \big(\rho_x(V^i_t)(1 - x^i_t) - \zeta_x(V^i_t)\,x^i_t\big)\,dt + \sqrt{\big|\rho_x(V^i_t)(1 - x^i_t) + \zeta_x(V^i_t)\,x^i_t\big|}\;\chi(x^i_t)\,dW^{i,x}_t, \qquad x = n, m, h.$$

This is the network above with $b_{\alpha\gamma}$ and $\beta_{\alpha\gamma}$ having first components $-\bar J_{\alpha\gamma}(V - \bar V_{\alpha\gamma})\,y'$ and $-\sigma^J_{\alpha\gamma}(V - \bar V_{\alpha\gamma})\,y'$, where $V$ is the potential of the postsynaptic and $y'$ the synaptic variable of the presynaptic neuron. Its mean-field equation is the system for $(V^\alpha, q^\alpha, y^\alpha)$ obtained by replacing each average $\frac{1}{N_\gamma}\sum_{j:\,p(j)=\gamma} y^j_t$ by $\mathbb E[y^\gamma_t]$, the indices $i$ by $\alpha$, and the Brownian motions by independent $B^{\alpha\gamma}$, $W^{\alpha,V}$, $W^{\alpha,y}$, $W^{\alpha,x}$.

**Hypotheses.** For every population $\alpha$:

- (A1) $\chi$ is bounded and Lipschitz with compact support in $(0, 1)$; the functions $\rho_x, \zeta_x$ are Lipschitz and bounded, and $\rho_x(v) \wedge \zeta_x(v) \ge \nu > 0$ for all $v$;
- (A2) $S_\alpha(v) = C/(1 + e^{-\lambda(v - \delta)})$ with $C, \lambda, \delta > 0$, and $a^\alpha_r, a^\alpha_d > 0$;
- (A3) $F_\alpha$ is continuous, one-sided Lipschitz in $v$ and Lipschitz in $q$: there are $L > 0$ and $M \ge 0$ with $\big(F_\alpha(t, v, q) - F_\alpha(t, v', q)\big)(v - v') \le L(v - v')^2 - M(v, v')(v - v')^2$ and $|F_\alpha(t, v, q) - F_\alpha(t, v, q')| \le L\|q - q'\|$ for $t \in [0, T]$;
- (A4) the initial conditions are independent and identically distributed within each population, $V^\alpha_0$ has moments of every order, and $y^\alpha_0$ and the gating variables take values in $[0, 1]$.

The FitzHugh–Nagumo drift $F_\alpha(v, w) = -\tfrac13 v^3 + v - w$ satisfies (A3) with $L = 1$ and $M(v, v') = \tfrac13(|v| - |v'|)^2$.

**Theorem (well-posedness).** Under (A1)–(A4), for every $T > 0$ the network system and its mean-field equation have unique pathwise solutions on $[0, T]$, with $\mathbb E\big[\sup_{t \le T}\|(V_t, q_t, y_t)\|^2\big] < \infty$, and their components $y$, $n$, $m$, $h$ take values in $[0, 1]$ for all $t \in [0, T]$. The same holds when the maximal conductances are positive Cox–Ingersoll–Ross processes $dJ^{\alpha\gamma}_t = \theta_{\alpha\gamma}(\bar J_{\alpha\gamma} - J^{\alpha\gamma}_t)\,dt + \sigma^J_{\alpha\gamma}\sqrt{J^{\alpha\gamma}_t}\,dB^{\alpha\gamma}_t$ with initial laws supported in $(0, \infty)$ and moments of every order, in place of the white-noise fluctuation.

The classical Hodgkin–Huxley drift does not satisfy (A3); the source states that the result extends to it by adding standard localisation arguments, without writing them out.

## Depends on

- [The FitzHugh–Nagumo vector field](../../fitzhugh-nagumo-model/field.md)
- [The Hodgkin–Huxley vector field](../../hodgkin-huxley-model/field.md)

## Expansion

The counterexample fails here because the law enters only through $\mathbb E[y^\gamma_t]$, a bounded functional that depends Lipschitz-continuously on the law, and because $F_\alpha$ is one-sided Lipschitz, not merely locally Lipschitz. The variables $y$, $n$, $m$, $h$ stay in $[0, 1]$: $\chi$ vanishes outside $(0, 1)$, and the drift points inward at $0$ and $1$, so Itô's formula applied to a smooth approximation of $\mathbf 1_{(-\infty, 0)}$ shows the negative part is indistinguishable from $0$, and likewise above $1$. The coefficients are locally Lipschitz, since $\lambda_1(1 - z) + \lambda_2 z > 0$ on $[0, 1]$ for $\lambda_1, \lambda_2 > 0$, so pathwise solutions exist up to explosion; the one-sided Lipschitz bound and Itô's formula bound the moments, so there is no explosion. For the mean-field equation, freeze $\mathbb E[y^\gamma_t]$ as a continuous function, solve, and let $\Phi$ send a law $\pi$ on path space to the law of the solution driven by $\bar y^{(\pi)}_t$, which is explicit in $\mathbb E_\pi[S_\gamma(V^\gamma_s)]$, $s \le t$, by the linear equation for $\mathbb E[y^\gamma_t]$. Coercivity ($\nu > 0$) makes the square-root diffusion coefficients Lipschitz on $[0, 1]$, and with the one-sided Lipschitz bound, Itô's formula gives $W_T^2(\Phi(\pi_1), \Phi(\pi_2)) \le K_T \int_0^T W_s^2(\pi_1, \pi_2)\,ds$ in the Wasserstein-2 distance on paths, so $\Phi$ has a unique fixed point by Sznitman's argument.

## Sources

- M. Bossy, O. Faugeras, D. Talay, "Clarification and complement to 'Mean-field description and propagation of chaos in networks of Hodgkin–Huxley and FitzHugh–Nagumo neurons'", *The Journal of Mathematical Neuroscience* 5 (2015) 19. Introduction (the counterexample, credited to M. Scheutzow), Section 2 (models (1)–(9), Hypothesis 2.1, Remarks 2.2 and 2.4), Section 3 (Proposition 3.3), Section 4 (Propositions 4.1 and 4.3, Remark 4.4). <https://doi.org/10.1186/s13408-015-0031-8>. PMCID: PMC4556725.
- M. Scheutzow, "Uniqueness and nonuniqueness of solutions of Vlasov–McKean equations", *Journal of the Australian Mathematical Society (Series A)* 43 (1987) 246–256, Counterexample 2. <https://doi.org/10.1017/S1446788700029384>.
- J. Baladron, D. Fasoli, O. Faugeras, J. Touboul, "Mean-field description and propagation of chaos in networks of Hodgkin–Huxley and FitzHugh–Nagumo neurons", *The Journal of Mathematical Neuroscience* 2 (2012) 10. Section 2 (network models) and Section 3.1 (mean-field and McKean–Vlasov–Fokker–Planck equations, Eqs. 22–24); its well-posedness theorem under general locally Lipschitz hypotheses is corrected by the first source. <https://doi.org/10.1186/2190-8567-2-10>. PMCID: PMC3497713.
