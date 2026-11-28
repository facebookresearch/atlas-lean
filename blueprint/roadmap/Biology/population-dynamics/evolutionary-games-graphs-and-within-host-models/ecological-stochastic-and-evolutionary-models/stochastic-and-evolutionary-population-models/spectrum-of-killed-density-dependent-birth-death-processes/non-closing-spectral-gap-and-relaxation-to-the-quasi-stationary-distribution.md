# Non-closing spectral gap and relaxation to the quasi-stationary distribution

**Setting.** Let $X^{(K)}$ be the density-dependent birth–death process with rates $Kb(n/K)$, $Kd(n/K)$, killed at $0$, under the assumptions of the large-population spectral limit: $0$ repelling ($b'(0)>d'(0)>0$), a unique attracting positive equilibrium $x_*$ ($b(x_*)=d(x_*)$, $b'(x_*)<d'(x_*)$). Write $-\rho^{(K)}_0>-\rho^{(K)}_1$ for the two leading eigenvalues of the killed generator in $\ell^2(\pi^{(K)})$, $\psi^{(K)}_0$ for the leading normalized eigenvector, $\nu^{(K)}$ for the quasi-stationary distribution, and $S^{(K)}_tf(n)=\mathbb{E}_n[f(X^{(K)}_t)\mathbf{1}_{\{T_0>t\}}]$ for the killed semigroup.

**Corollary (spectral gap).**

$$\lim_{K\to\infty}\big(\rho^{(K)}_1-\rho^{(K)}_0\big)=\min\big\{b'(0)-d'(0),\ d'(x_*)-b'(x_*)\big\}>0 .$$

So, although the extinction rate $\rho^{(K)}_0$ is exponentially small in $K$, the gap does not close (an earlier general bound only gave a gap of order $1/\log K$).

**Relaxation.** For $\psi\in\ell^2(\pi^{(K)})$ and $t>0$,

$$\Big\|e^{\rho^{(K)}_0t}S^{(K)}_t\psi-\psi^{(K)}_0\,\langle\psi^{(K)}_0,\mathbf{1}\rangle_{\pi^{(K)}}\,\nu^{(K)}(\psi)\Big\|_{\ell^2(\pi^{(K)})}\le\|\psi\|_{\ell^2(\pi^{(K)})}\,e^{-(\rho^{(K)}_1-\rho^{(K)}_0)t}.$$

For the $Q$-process (the process conditioned never to go extinct), with semigroup $R^{(K)}_tg=e^{\rho^{(K)}_0t}(\psi^{(K)}_0)^{-1}S^{(K)}_t(g\psi^{(K)}_0)$ and invariant law $\mathfrak{m}^{(K)}(g)=\nu^{(K)}(\psi^{(K)}_0g)$, correlations decay at the same rate: for $g_1,g_2\in\ell^2(\mathfrak{m}^{(K)})$,

$$\Big|\int R^{(K)}_tg_1\,g_2\,d\mathfrak{m}^{(K)}-\int g_1\,d\mathfrak{m}^{(K)}\int g_2\,d\mathfrak{m}^{(K)}\Big|\le\|g_1\|\,\|g_2\|\,e^{-(\rho^{(K)}_1-\rho^{(K)}_0)t}.$$

Hence relaxation times to quasi-stationarity converge to a finite limit as $K\to\infty$.

**Examples.** Logistic, $b=\lambda x$, $d=x(\mu+x)$, $\lambda>\mu$: gap $\to\lambda-\mu$. Ayala–Gilpin–Ehrenfeld, $d=x(\mu+x^\theta)$ with $\theta\in(0,1)$: gap $\to\theta(\lambda-\mu)$. Smith's model, $b=\lambda x/(1+x)$, $d=x(\mu+x)/(1+x)$: gap $\to(\lambda-\mu)/(1+\lambda-\mu)$.

## Depends on

- [Large-population limit of the spectrum of a killed birth–death process](large-population-limit-of-the-spectrum-of-a-killed-birth-death-process.md)

## Expansion

The limiting spectrum is $\{0\}\cup S_1\cup S_2$ with $S_1=(d'(x_*)-b'(x_*))\mathbb{Z}_{\ge0}$ and $S_2=(b'(0)-d'(0))\mathbb{Z}_{>0}$; its smallest nonzero point is the minimum of the two slopes, which is the limit of $\rho_1-\rho_0$ because $\rho_0\to0$. The slower of two mechanisms sets the relaxation: Ornstein–Uhlenbeck relaxation of fluctuations around $Kx_*$, or the decay of a near-extinction excursion governed by the linearized branching process. The bounds themselves are the spectral theorem for the self-adjoint killed generator, after projecting off the leading eigenvector; the $Q$-process statement follows by the Doob $h$-transform with $h=\psi^{(K)}_0$, which is an isometry between $\ell^2(\mathfrak{m}^{(K)})$ and $\ell^2(\pi^{(K)})$ up to the constant $\langle\psi^{(K)}_0,\mathbf{1}\rangle_{\pi^{(K)}}$.

## Sources

- J. -r. Chazottes, P. Collet and S. Méléard, "Large population limit of the spectrum of killed birth-and-death processes", Journal of Functional Analysis 285 (2023), 110092, <https://doi.org/10.1016/j.jfa.2023.110092>; numbering as in arXiv:2204.10748: Corollary 1.3 and Proposition 1.4 (Section 1.5).
