# Age-structured SIR as the fast-rewiring limit of a network epidemic

**Stochastic model.** $n$ individuals are partitioned into $m$ age groups $\mathcal A_1,\dots,\mathcal A_m$ with $|\mathcal A_i|$ proportional to $n$. Each ordered pair $(a,b)\in\mathcal A_i\times\mathcal A_j$ carries a directed contact edge that is re-drawn at the times of a rate-$\lambda^{(n)}$ Poisson process, existing after each redraw with probability $\rho_{ij}/n$ independently of the past (so mean degrees stay bounded). An infected node of group $j$ infects a susceptible neighbour of group $i$ at rate $B_{ij}$ along a present edge, and an infected node of group $i$ recovers at rate $\gamma_i$. Let $s_i^{(n)}(t),\beta_i^{(n)}(t)$ be the fractions of the population that are susceptible and infected members of group $i$.

**Mean-field ODE (age-structured SIR).** With $A_{ij}=\rho_{ij}B_{ij}$,

$$\dot y_i=-y_i\sum_{j=1}^mA_{ij}w_j,\qquad \dot w_i=y_i\sum_{j=1}^mA_{ij}w_j-\gamma_iw_i .$$

**Proposition (contact probability bounds).** For susceptible $a\in\mathcal A_i$ and infected $b\in\mathcal A_j$, the conditional probability $\chi_{ij}$ that the edge $(a,b)$ is present given the epidemic state satisfies, for all $t\ge0$,

$$\frac{\rho_{ij}}n\Big(1-\frac{B_{ij}}{\lambda^{(n)}}\big(1-e^{-\lambda^{(n)}t}\big)\Big)\le\chi_{ij}\le\frac{\rho_{ij}}n .$$

**Theorem (mean-field convergence).** If $\lambda^{(n)}\to\infty$ and $s_i^{(n)}(0)\to s_{i,0}$, $\beta_i^{(n)}(0)\to\beta_{i,0}$, then for every $i$ and every finite horizon,

$$\lim_{n\to\infty}\mathbb E\Big[\big\|\big(s_i^{(n)}(t),\beta_i^{(n)}(t)\big)-\big(y_i(t),w_i(t)\big)\big\|_2^2\Big]=0,$$

where $(y,w)$ solves the ODE with $y_i(0)=s_{i,0}$, $w_i(0)=\beta_{i,0}$.

**Theorem (converse).** If instead $\lambda^{(n)}\to\lambda_\infty<\infty$, there is no time interval on which all $y_p,w_p$ stay positive and the network fractions converge in probability to the ODE solution: convergence fails on every such interval.

## Expansion

The exact moment equations read $\frac{d}{dt}\mathbb E[s_i]=-\sum_jB_{ij}\mathbb E[n\chi_{ij}s_i\beta_j]$, so the ODE appears exactly when $n\chi_{ij}\to\rho_{ij}$. Conditioning on an infected–susceptible pair biases the edge between them towards absence, because a present edge would likely already have transmitted; the bias is erased only if the edge is redrawn before transmission, which happens with probability $1-O(B_{ij}/\lambda)$. Second-moment equations show the variances are $O(1/n)$, giving $L^2$ convergence. With bounded $\lambda$ the depletion of infected–susceptible contacts persists, and the effective contact rate is strictly below $\rho_{ij}B_{ij}$, so the ODE is the wrong limit. The rate of convergence is governed by $B_{ij}/\lambda^{(n)}$ and $1/n$.

## Sources

- Rohit Parasnis, Ryosuke Kato, Amol Sakhale, Massimo Franceschetti and Behrouz Touri, "Usefulness of the Age-Structured SIR Dynamics in Modelling COVID-19", arXiv:2203.05111: Section "Problem formulation" (age-structured SIR and the stochastic network model), Section "Main result" (main convergence theorem and the moment-equation and contact-probability propositions), Section "A converse result" (converse theorem). <https://doi.org/10.48550/arXiv.2203.05111> Published version: 2021 60th IEEE Conference on Decision and Control (CDC) (2021) 5508–5513, <https://doi.org/10.1109/cdc45484.2021.9683725>.
