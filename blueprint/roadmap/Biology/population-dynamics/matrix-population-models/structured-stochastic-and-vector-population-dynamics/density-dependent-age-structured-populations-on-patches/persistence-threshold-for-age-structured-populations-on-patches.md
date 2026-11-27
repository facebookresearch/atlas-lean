# Persistence threshold for density-dependent age-structured populations on connected patches

**Model.** The density $n_k(a,t)$ of individuals of age $a$ on patch $k=1,\dots,N$ satisfies

$$\partial_tn_k+\partial_an_k=-\mu_k(a,t)\,n_k\Big(1+\frac{n_k}{L_k(a,t)}\Big)+\sum_{j=1}^ND_{kj}(a,t)\,n_j,\qquad n_k(0,t)=\int_0^\infty m_k(a,t)\,n_k(a,t)\,da,$$

with initial data $n_k(a,0)=f_k(a)$. Here $\mu_k$ is mortality, $L_k>0$ a regulating function (density-dependent mortality $\mu_kn_k^2/L_k$), $m_k$ fertility, and $D=(D_{kj})$ a dispersal matrix with $D_{kj}\ge0$ for $k\ne j$, $D_{kk}\le0$, assumed **essentially positive**: every patch can be reached from every other through a chain of positive dispersal rates (the dispersal graph is strongly connected).

**Reduction.** The newborn vector $\rho(t)=(n_k(0,t))_k$ solves a nonlinear renewal equation $\rho=\mathcal K\rho+\mathcal Ff$. In the time-independent case the stationary newborn vectors solve the *characteristic equation* $\rho=\mathcal K\rho$, $(\mathcal K\rho)_k=\int_0^\infty m_k(a)\Phi_k(a;\rho)\,da$, where $\Phi(\cdot;\rho)$ solves the age ODE system started at $\rho$. The **net reproductive map** is its linearization at zero,

$$\mathscr R_0\rho=\lim_{\varepsilon\to0}\frac1\varepsilon\mathcal K(\varepsilon\rho),$$

a strongly positive linear map on $\mathbb R^N$ whose spectral radius $\sigma(\mathscr R_0)$ is its Perron eigenvalue (for $N=1$ it is $R_0=\int_0^\infty m(a)e^{-\int_0^a\mu}\,da$).

**Theorem (characteristic equation).** If $\sigma(\mathscr R_0)\le1$, the characteristic equation has only the trivial solution $\rho^*=0$. If $\sigma(\mathscr R_0)>1$, it has exactly one nontrivial solution $\rho^*$, and all its components are positive.

**Theorem (large-time behaviour).** Problem has a unique bounded continuous solution. In the time-independent case, if $\sigma(\mathscr R_0)\le1$ then $\rho(t)\to0$ and the total population $N(t)=\int_0^\infty n(a,t)\,da\to0$ (extinction on every patch); if $\sigma(\mathscr R_0)>1$ then $\rho(t)\to\rho^*$ and $N(t)\to\int_0^\infty\Phi(a;\rho^*)\,da$, so the population persists on **all** patches. The same dichotomy holds for time-periodic coefficients with $\mathscr R_0$ replaced by the periodic net reproductive operator. For irregularly varying coefficients bracketed for large $t$ by $T$-periodic ones, $m^-\le m\le m^+$, $\mu^+\le\mu\le\mu^-$, and likewise for $L_k$ and $D_{kj}$ (the source's (10)), let $\widetilde{\mathscr R}_0^\pm$ be the periodic net reproductive operators of the two bracketing periodic problems and $\rho^\pm$ the $T$-periodic solutions of their characteristic equations: if $\sigma(\widetilde{\mathscr R}_0^+)\le1$ then $\rho(t)\to0$, and if $\sigma(\widetilde{\mathscr R}_0^-)>1$ then for every $\varepsilon>0$, $\rho^-(t)-\varepsilon\le\rho(t)\le\rho^+(t)+\varepsilon$ for large $t$.

## Expansion

Strong connectivity makes the linearized age ODE cooperative and irreducible, so a comparison lemma gives strict positivity of solutions and Krein–Rutman applies to $\mathscr R_0$. The map $\mathcal K$ is monotone and strictly sublinear, $\mathcal K(\theta\rho)>\theta\mathcal K(\rho)$ for $\theta\in(0,1)$, because density-dependent mortality bites harder at higher densities; for such concave monotone maps, a positive fixed point exists exactly when the derivative at zero has spectral radius above one, and it is unique and globally attracting on the positive cone. Since every patch is reachable, positive newborns on one patch propagate to all, which is why persistence or extinction is simultaneous across patches.

## Sources

- Vladimir Kozlov, Sonja Radosavljevic, Vladimir G. Tkachev, Uno Wennergren, "Persistence analysis of the age-structured population model on several patches", in Proceedings of the 16th International Conference on Computational and Mathematical Methods in Science and Engineering (CMMSE 2016), Almería, vol. II (2016), 717–727 (the proceedings have no DOI). Published version of arXiv:1608.04492, cited next; locators there refer to the arXiv version.
- Vladimir Kozlov, Sonja Radosavljevic, Vladimir G. Tkachev, Uno Wennergren, "Persistence analysis of the age-structured population model on several patches", arXiv:1608.04492 (2016): model in Section 2, Theorem 1, Lemma 2, Theorem 3, Section 4 (periodic environment), Theorem 4 (irregular environment). <https://doi.org/10.48550/arXiv.1608.04492>
