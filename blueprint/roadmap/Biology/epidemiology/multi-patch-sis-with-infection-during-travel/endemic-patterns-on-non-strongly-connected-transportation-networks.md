# Endemic patterns on non-strongly-connected transportation networks

Consider $n \ge 2$ regions $\Omega = \{1,\dots,n\}$. In region $j$ let $N_j$ be the total population and $I_j$ the infectives, with recruitment $A_j > 0$, death rate $d_j > 0$, recovery $\delta_j \ge 0$ and contact rate $\beta_j > 0$ (standard incidence). Individuals (susceptible and infective alike) leave region $k$ for region $j$ at per-capita rate $\alpha_{jk} \ge 0$, travel for time $\tau_{jk} \ge 0$ without births or deaths, and during the journey follow SIS dynamics with contact rate $\beta^T_{jk}$ and recovery $\delta^T_{jk}$ (with $\beta^T_{jk} \ne \delta^T_{jk}$). With $l_j = \sum_k \alpha_{kj}$, solving the travel stage along characteristics gives the delay system

$$\dot N_j = A_j - (d_j + l_j) N_j + \sum_{k} \alpha_{jk} N_k(t - \tau_{jk}),$$

$$\dot I_j = I_j\Bigl(\beta_j - d_j - \delta_j - l_j - \beta_j \frac{I_j}{N_j}\Bigr) + \sum_k \frac{\alpha_{jk} e^{(\beta^T_{jk} - \delta^T_{jk})\tau_{jk}} I_k(t - \tau_{jk})}{1 + \frac{e^{(\beta^T_{jk} - \delta^T_{jk})\tau_{jk}} - 1}{\beta^T_{jk} - \delta^T_{jk}}\, \beta^T_{jk}\, \frac{I_k(t - \tau_{jk})}{N_k(t - \tau_{jk})}}.$$

The next-generation matrix is

$$M = \operatorname{diag}\Bigl(\frac{\beta_j}{d_j + \delta_j + l_j}\Bigr) + \Bigl(\frac{\alpha_{jk}\, e^{(\beta^T_{jk} - \delta^T_{jk})\tau_{jk}}}{d_k + \delta_k + l_k}\Bigr)_{j,k}, \qquad \mathcal R_0 = \rho(M),$$

and $\max_j \beta_j/(d_j + \delta_j + l_j) \le \mathcal R_0$.

1. **Total population.** The $N$-subsystem has a unique positive equilibrium $N^+$, which is globally asymptotically stable.
2. **Strongly connected network.** If the matrix $(\alpha_{jk})$ is irreducible, then for $\mathcal R_0 \le 1$ the disease-free equilibrium $(N^+, 0)$ is globally asymptotically stable, and for $\mathcal R_0 > 1$ a unique endemic equilibrium with all $I_j^+ > 0$ is globally asymptotically stable for all initial data with some infection.
3. **Block classification.** In general, order regions so that $(\alpha_{jk})$ is block lower triangular with irreducible (or $1 \times 1$) diagonal blocks $1,\dots,m$, and let $\mathcal R_p$ be the spectral radius of the $p$-th diagonal block of $M$. Block $1$ is endemic iff $\mathcal R_1 > 1$. For $p \ge 2$: if some endemic block $h < p$ has a transport connection into block $p$, then block $p$ is endemic; otherwise block $p$ is disease free iff $\mathcal R_p \le 1$.
4. **Global attractor.** The system always has a globally asymptotically stable equilibrium, whose pattern of endemic and disease-free blocks is determined recursively by item 3.

## Expansion

The total population satisfies a linear cooperative delay system whose coefficient matrix is a nonsingular M-matrix, giving item 1. Along $N^+$ the infective equations are asymptotically autonomous; the limit system is cooperative and strictly sublinear, so the Zhao–Jing threshold theorem gives a dichotomy, and the sign of the spectral bound of the linearisation agrees with the sign of $\mathcal R_0 - 1$ by the next-generation argument. For a reducible network, block $1$ receives no inflow, so item 2 applies to it. Assuming blocks $1,\dots,p-1$ have converged, the inflow into block $p$ converges either to zero or to a positive forcing; positive forcing makes the zero state of block $p$ impossible as a limit and the forced cooperative sublinear system has a unique positive attractor, while zero forcing reduces block $p$ to its own threshold $\mathcal R_p$. Induction over blocks gives items 3–4: an endemic block seeds every block downstream of it, so partially endemic equilibria coexist with disease-free blocks upstream. For example, a region with local reproduction number below one stays endemic if it receives immigrants from an endemic region.

## Sources

- Y. Nakata, G. Röst, "Global analysis for spread of infectious diseases via transportation networks", *Journal of Mathematical Biology* (2015), Sections 2–5 (Eqs. (2.8), (3.2), (4.1)–(4.2), Propositions 3.1–3.2, Theorems 4.2, 5.3, 5.4, Propositions 5.8, 5.10, Theorem 5.11), <https://doi.org/10.1007/s00285-014-0801-z> (PMC7080142).
