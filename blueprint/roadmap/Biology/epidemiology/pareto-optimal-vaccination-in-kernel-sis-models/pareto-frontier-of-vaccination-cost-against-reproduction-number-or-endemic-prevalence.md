# Pareto frontier of vaccination cost against reproduction number or endemic prevalence

**Setting.** Let $(\Omega,\mathcal{F},\mu)$ be a probability space of individual features, $k\ge 0$ a transmission rate kernel on $\Omega^2$ and $\gamma\in L^\infty_+$ a recovery rate with $\|k/\gamma\|_{\infty,q}<\infty$ for some $q>1$. The infinite-dimensional SIS model is

$$\partial_t u_t=(1-u_t)\,T_k(u_t)-\gamma u_t,\qquad T_k(g)(x)=\int_\Omega k(x,y)g(y)\,\mu(dy),$$

with $u_t(x)\in[0,1]$ the probability that an individual of feature $x$ is infected. A vaccination strategy is $\eta\in\Delta=\{\eta\in L^\infty:0\le\eta\le1\}$, where $\eta(x)$ is the fraction of feature-$x$ individuals left **unvaccinated**. With next generation kernel $\mathrm{k}(x,y)=k(x,y)/\gamma(y)$, the effective reproduction number is the spectral radius $R_e(\eta)=\rho(T_{\mathrm{k}\eta})$, where $(\mathrm{k}\eta)(x,y)=\mathrm{k}(x,y)\eta(y)$, so $R_e(1)=R_0$. If $\mathfrak{g}_\eta$ is the maximal equilibrium of the model with kernel $k\eta$, the endemic prevalence is $I(\eta)=\int_\Omega \mathfrak{g}_\eta\,\eta\,d\mu$. The uniform cost is $C(\eta)=\int_\Omega(1-\eta)\,d\mu$. Equip $\Delta$ with the weak-$*$ topology of $L^\infty$ (in which it is compact).

A strategy $\eta_\star$ is *Pareto optimal* for a loss $L\in\{R_e,I\}$ if no strategy has strictly smaller cost without strictly larger loss, nor strictly smaller loss without strictly larger cost. Let $L^\star(c)=\min\{L(\eta):C(\eta)\le c\}$ and $C^\star(\ell)=\min\{C(\eta):L(\eta)\le\ell\}$, and $\mathcal{F}_L$ the set of outcomes $(C(\eta_\star),L(\eta_\star))$ of Pareto optimal strategies.

**Theorem.**

1. $R_e$ and $I$ are continuous on $\Delta$ for the weak topology, non-decreasing, and sub-homogeneous: $L(\lambda\eta)\le\lambda L(\eta)$ for $\lambda\in[0,1]$. Moreover $I(\eta)=0$ if and only if $R_e(\eta)\le1$.
2. For every cost budget $c$ a loss minimizer exists, and for every loss level $\ell$ a cost minimizer exists; Pareto optimal strategies exist for both losses, and the set of Pareto optimal strategies is weakly compact.
3. For $L\in\{R_e,I\}$, $C^\star$ is continuous and decreasing on $[0,\max L]$, $L^\star$ is continuous, decreasing on $[0,C^\star(0)]$ and zero beyond, and the Pareto frontier is the connected curve

$$\mathcal{F}_L=\{(c,L^\star(c)):c\in[0,C^\star(0)]\}=\{(C^\star(\ell),\ell):\ell\in[0,\max L]\}.$$

## Expansion

Weak continuity is the analytic core. For $R_e$, the operators $T_{\mathrm{k}\eta}$ are compact, and weak convergence $\eta_n\to\eta$ makes $T_{\mathrm{k}\eta_n}$ converge to $T_{\mathrm{k}\eta}$ after composing with a fixed compact operator; the spectrum of compact operators is continuous along such sequences (in Hausdorff distance), which yields continuity of $\rho$. Continuity of $I$ uses the characterization of the maximal equilibrium $\mathfrak{g}_\eta$ as the unique nonzero equilibrium $h$ with $R_e$ of the residual susceptible kernel at most one. Existence of optima then follows from compactness of $\Delta$ and lower semicontinuity. Monotonicity and sub-homogeneity of the losses rule out local minima with positive loss, which forces the constraints to bind and gives the graph description and connectedness of the frontier.

## Sources

- Jean-François Delmas, Dylan Dronnier, Pierre-André Zitt, "Targeted Vaccination Strategies for an Infinite-dimensional SIS Model", arXiv:2103.10330 (2021): Section 1 (model, Equations for the SIS dynamics, $R_e$ and $I$, and the main results on continuity and the Pareto frontier), Section 4 (Propositions on basic properties of $R_e$ and $I$ and the continuity theorems), Section 5 (existence of optimal strategies, single- versus bi-objective problems, compactness of Pareto optima). <https://doi.org/10.48550/arXiv.2103.10330>
