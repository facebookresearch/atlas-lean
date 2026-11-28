# Likelihood of an epidemic with partially observed contact tracing

**Model.** Individuals $j$ have infection times $I_j$, notification (detection) times $N_j$ and removal times $R_j$; $\kappa$ is the index case, $T_{\mathrm{obs}}$ the observation time, and $\mathcal Y(t)$ the set of infected individuals (infectious or notified) at time $t$. Along each of $K$ contact networks, contacts between $i$ and $j$ occur as a Poisson process with known rate $r_{ij}^{(k)}$; a contact from infected $i$ to susceptible $j$ transmits with probability $q(i;\boldsymbol\xi,t-I_i)\,s(j;\boldsymbol\eta)\,p_k$, where $q$ is infectivity, $s$ susceptibility and $p_k$ the per-contact transmission probability of network $k$. The infection hazard on $j$, $\lambda_j(t)$, combines these thinned contact processes with any other (e.g. spatial) transmission terms. The detection delay $N_j - I_j$ has density $f_D$ and distribution function $F_D$.

**Contact-tracing data.** For each detected case $j$, contacts are recorded only in a contact-tracing window $\mathcal W_j$; $C_{ijk}(t)$ counts contacts between $i$ and $j$ on network $k$, and

$$

Z_{ijk}(t) = \mathbf 1[I_j = t]\,\log\big(q(i;\boldsymbol\xi,I_j - I_i)\,s(j;\boldsymbol\eta)\,p_k\big) + \big(1 - \mathbf 1[I_j \ge t]\big)\log\big(1 - q(i;\boldsymbol\xi,I_j - I_i)\,s(j;\boldsymbol\eta)\,p_k\big).

$$

**Theorem.** If contacts are observed only within the windows $\mathcal W_j$ and the contact rates $r_{ij}^{(k)}$ are known, the likelihood given the observed data is obtained by taking the expectation over the unobserved contacts outside the windows, and equals

$$

\begin{aligned}
L(\mathbf I,\mathbf N,\mathbf R,\boldsymbol{\mathcal C} \mid \boldsymbol\theta) &= \prod_{j : I_j \in \mathcal W_j} \exp\Big[\int_{\mathcal W_j}\sum_{i\in\mathcal Y(t)}\sum_{k=1}^K Z_{ijk}(t)\,dC_{ijk}(t)\Big]\\
&\quad\times \prod_{\substack{j : I_j \in \mathcal W_j^c\\ j \ne \kappa}} \lambda_j(I_j^-)\,\exp\Big[-\int_{\mathcal W_j^c}\lambda_j(t)\,dt\Big]\\
&\quad\times \prod_{j : N_j \le T_{\mathrm{obs}}} f_D(N_j - I_j) \times \prod_{j : N_j > T_{\mathrm{obs}}}\big[1 - F_D(T_{\mathrm{obs}} - I_j)\big].
\end{aligned}

$$

Inside a window each observed contact contributes a Bernoulli term (transmitted at the infection time, not transmitted before it); outside, contacts are integrated out and the usual continuous-time hazard likelihood of the epidemic applies.

## Expansion

With all contacts observed, the likelihood of the transmission parameters is a product over contacts of Bernoulli probabilities, written compactly as $\exp\int Z\,dC$. Splitting time for each individual into the window $\mathcal W_j$ and its complement, the contact processes in the two parts are independent given the parameters, so the expectation over unobserved contacts factorizes. Outside the window, a Poisson contact process thinned by the transmission probability is again Poisson, with rate equal to the corresponding part of $\lambda_j(t)$, which produces the hazard-times-survival terms. The detection terms are unchanged. The likelihood is used inside a Markov chain Monte Carlo sampler that also imputes unobserved infection times, and simulations based on the British poultry industry show that traced contacts sharpen the posterior of the $p_k$ and improve risk prediction.

## Sources

- Chris Jewell, Gareth Roberts, "Enhancing Bayesian risk prediction for epidemics using contact tracing", arXiv (2012); Biostatistics (2012). Section 3 (model review), Section 4 (Theorem 1 and its proof in the supplementary material), Section 5. <https://doi.org/10.48550/arXiv.1203.3366>. Published version: Biostatistics 13(4) (2012), 567–579, <https://doi.org/10.1093/biostatistics/kxs012>; locators above refer to the arXiv version.
