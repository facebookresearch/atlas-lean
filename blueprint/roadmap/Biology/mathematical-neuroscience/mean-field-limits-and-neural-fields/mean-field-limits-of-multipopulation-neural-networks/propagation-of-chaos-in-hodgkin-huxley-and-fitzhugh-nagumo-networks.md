# Propagation of chaos in Hodgkin–Huxley and FitzHugh–Nagumo networks

**Network.** $N$ neurons are divided into populations $\alpha \in \mathcal P$ of sizes $N_\alpha$, and $p(i)$ is the population of neuron $i$. Neuron $i$ with $p(i) = \alpha$ has membrane potential $V^i_t$, maximal synaptic conductances $J^{i\gamma}_t$ ($\gamma \in \mathcal P$), a proportion $y^i_t$ of available neurotransmitter, and either the recovery variable $\mathbf x^i = (w^i)$ of the [FitzHugh–Nagumo model](../../fitzhugh-nagumo-model/README.md) or the gating variables $\mathbf x^i = (n^i, m^i, h^i)$ of the [Hodgkin–Huxley model](../../hodgkin-huxley-model/README.md). With sign-preserving conductances,

$$\begin{aligned}
dV^i_t &= F_\alpha(t, V^i_t, \mathbf x^i_t)\,dt - \sum_{\gamma\in\mathcal P}(V^i_t - \overline V^{\alpha\gamma})\,\frac{J^{i\gamma}_t}{N_\gamma}\sum_{j:\,p(j)=\gamma} y^j_t\,dt + \sigma_\alpha\,dW^{i,V}_t,\\
dJ^{i\gamma}_t &= \theta_{\alpha\gamma}\big(\bar J^{\alpha\gamma} - J^{i\gamma}_t\big)\,dt + \sigma^J_{\alpha\gamma}\sqrt{J^{i\gamma}_t}\,dB^{i\gamma}_t,\\
dy^i_t &= \big(a^\alpha_r S_\alpha(V^i_t)(1 - y^i_t) - a^\alpha_d y^i_t\big)\,dt + \sqrt{\big|a^\alpha_r S_\alpha(V^i_t)(1 - y^i_t) + a^\alpha_d y^i_t\big|}\;\chi(y^i_t)\,dW^{i,y}_t,
\end{aligned}$$

coupled with $dw^i_t = c_\alpha(V^i_t + a_\alpha - b_\alpha w^i_t)\,dt$ (FitzHugh–Nagumo) or, for $x = n, m, h$ (Hodgkin–Huxley),

$$dx^i_t = \big(\rho_x(V^i_t)(1 - x^i_t) - \zeta_x(V^i_t)x^i_t\big)\,dt + \sqrt{\big|\rho_x(V^i_t)(1 - x^i_t) + \zeta_x(V^i_t)x^i_t\big|}\;\chi(x^i_t)\,dW^{i,x}_t,$$

with all Brownian motions independent and all quantities without a time index constant parameters. The mean-field system for $R^\alpha = (V^\alpha, (J^{\alpha\gamma})_\gamma, y^\alpha, \mathbf x^\alpha)$, $\alpha \in \mathcal P$, is the same system with $\frac{1}{N_\gamma}\sum_{p(j)=\gamma}y^j_t$ replaced by $\mathbb E[y^\gamma_t]$ and one independent set of Brownian motions per population.

**Hypotheses.**
1. $\chi$ is bounded and Lipschitz with compact support in $(0,1)$; $\rho_x, \zeta_x$ are strictly positive, Lipschitz and bounded.
2. $S_\alpha(v) = C/(1 + e^{-\lambda(v - \delta)})$ with positive $C, \lambda, \delta$ depending on $\alpha$, and $a^\alpha_r, a^\alpha_d > 0$.
3. $F_\alpha$ is continuous, one-sided Lipschitz in $v$ and Lipschitz in $\mathbf x$: there are $L > 0$ and a positive map $M(v, v')$ with $(F_\alpha(t,v,\mathbf x) - F_\alpha(t,v',\mathbf x))(v - v') \le L(v - v')^2 - M(v,v')(v - v')^2$ and $|F_\alpha(t,v,\mathbf x) - F_\alpha(t,v,\mathbf x')| \le L\|\mathbf x - \mathbf x'\|$. The FitzHugh–Nagumo drift $F_\alpha(v, w) = -\tfrac13v^3 + v - w$ satisfies this with $L = 1$ and $M(v,v') = \tfrac13(|v| - |v'|)^2$.
4. The initial conditions are i.i.d. within each population; $V_0$ and $J_0$ have moments of every order, the laws of $y_0, n_0, m_0, h_0$ are supported in $[0,1]$, and that of $J_0$ in $(0,\infty)$.
5. (Coercivity) $\rho_x(v) \wedge \zeta_x(v) \ge \nu > 0$ for all $v$, for some $\nu$.

**Theorem.**
1. *Mean-field equation.* Under hypotheses 1–5, the mean-field system has a unique pathwise solution on every interval $[0,T]$, and $y^\alpha, n^\alpha, m^\alpha, h^\alpha$ take values in $[0,1]$.
2. *Propagation of chaos.* Assume moreover that each proportion $c_\gamma = N_\gamma/N$ is a nonzero constant independent of $N$. For each neuron $i$ with $p(i) = \alpha$ let $R^{i,N} = (V^i, (J^{i\gamma})_\gamma, y^i, \mathbf x^i)$, and let $\widetilde R^i$ be the solution of the mean-field equation of population $\alpha$ with the same initial condition, the same $J^{i\gamma}$ and the same Brownian motions $W^{i,\cdot}$, so that the $\widetilde R^i$ with $p(i) = \alpha$ are independent copies of $R^\alpha$. Then there is $C > 0$ such that for every such $N$ and every choice of one neuron $i_\alpha$ in each population, $\sqrt N\,\mathbb E\big[\sup_{0\le t\le T}\sum_{\alpha\in\mathcal P}|R^{i_\alpha,N}_t - \widetilde R^{i_\alpha}_t|^2\big] \le C$. Consequently, for every fixed $k$, the law of the states of $k$ neurons from each population converges to the corresponding product of mean-field laws: finitely many neurons become asymptotically independent.

The original paper of Baladron, Fasoli, Faugeras and Touboul states these results for general networks with locally Lipschitz intrinsic dynamics; the refereed correction of Bossy, Faugeras and Talay shows that its proof "involves an erroneous management of hitting times in combination with a truncation technique, and the limit system may not be well-defined under the too general hypothesis used by the authors", and proves the statements above for the FitzHugh–Nagumo and Hodgkin–Huxley networks only.

## Proof sketch

The functions $\chi$ vanishing outside $(0,1)$ and the signs of the drifts at $0$ and $1$ keep the proportions $y, n, m, h$ in $[0,1]$, which makes the square-root diffusion coefficients locally Lipschitz where they matter. Existence and pathwise uniqueness of the mean-field equation extend Sznitman's fixed-point method on path space; the one-sided Lipschitz condition replaces global Lipschitz continuity of the cubic or Hodgkin–Huxley drift. For the limit, couple each network neuron with an independent copy of the mean-field process driven by the same Brownian motions (Sznitman's coupling); the difference is controlled by the fluctuation of the empirical averages $\frac1{N_\gamma}\sum_j y^j$ around $\mathbb E[y^\gamma]$, which is $O(N^{-1/2})$ in mean square by independence of the coupled copies, with expectations taken only at the end because of the polynomial, non-Lipschitz part of the drift. This argument, given by Bossy, Faugeras and Talay, replaces the truncation argument of the original paper, which does not hold.

## Sources

- Mireille Bossy, Olivier Faugeras and Denis Talay, "Clarification and Complement to 'Mean-Field Description and Propagation of Chaos in Networks of Hodgkin–Huxley and FitzHugh–Nagumo Neurons'", *The Journal of Mathematical Neuroscience* 5 (2015), 19, <https://doi.org/10.1186/s13408-015-0031-8>. Preprint version: arXiv:1412.7728v5 (2015), Section 1 (the error in the original proof), Section 2 (the sign-preserving network model and its mean-field limit, Hypothesis 2.1), Proposition 4.3 (well-posedness of the mean-field system under the coercivity condition) and Proposition 4.5 (propagation of chaos), <https://doi.org/10.48550/arXiv.1412.7728>.
- Javier Baladron, Diego Fasoli, Olivier Faugeras and Jonathan Touboul, "Mean-field description and propagation of chaos in networks of Hodgkin-Huxley and FitzHugh-Nagumo neurons", *The Journal of Mathematical Neuroscience* 2 (2012), 10, <https://doi.org/10.1186/2190-8567-2-10>. Preprint version: arXiv:1110.4294 (2011), network and mean-field equations (the general form whose proof the correction above repairs only for these two models), <https://doi.org/10.48550/arXiv.1110.4294>.
