# Spectral maximum likelihood estimator of diffusivity in stochastic activator–inhibitor models

**Model.** On a box $\mathcal D=[0,L_1]\times\cdots\times[0,L_d]$ with periodic boundary conditions, on $H=\{u\in L^2(\mathcal D):\int u=0\}$, consider the semilinear stochastic PDE

$$\mathrm dX_t=\bigl(\theta_0\Delta X_t+F_{\theta_1,\dots,\theta_K}(X)\bigr)\mathrm dt+B\,\mathrm dW_t,\qquad B=\sigma(-\Delta)^{-\gamma},\ \gamma>d/4,$$

with $W$ a cylindrical Wiener process (space–time white noise), diffusivity $\theta_0>0$ and nuisance reaction parameters $\theta_{1:K}$. The key example ($d\le2$) is the FitzHugh–Nagumo-type activator–inhibitor system for intracellular actin waves,

$$\mathrm dU=\bigl(D_U\Delta U+k_1U(u_0-U)(U-a(|U|_{L^2})u_0)-k_2V\bigr)\mathrm dt+B\,\mathrm dW,\qquad \partial_tV=D_V\Delta V+\epsilon(bU-V),$$

where $a\in C^1_b(\mathbb R,\mathbb R)$ is bounded and continuously differentiable with bounded derivative, the inhibitor starts from $V_0=0$, and only the activator $U$ is observed. Eliminating $V$ by variation of constants (which uses $V_0=0$; a nonzero $V_0$ adds the term $e^{t(D_V\Delta-\epsilon)}V_0$) turns it into the form above with $\theta_0=D_U$, linear dependence on $(\theta_1,\theta_2,\theta_3)$, and a history-dependent (non-Markovian) term $-\int_0^te^{(t-r)(D_V\Delta-\epsilon)}U_r\,\mathrm dr$.

**Estimator.** Let $(\lambda_k,\Phi_k)$ be the eigenpairs of $-\Delta$, so that $\lambda_k\sim\Lambda k^{2/d}$, and let $X^N$ be the projection of $X$ onto the first $N$ eigenfunctions. With a free contrast parameter $\alpha$, the maximum likelihood equations for continuous observation of $X^N$ on $[0,T]$ give

$$\hat\theta^N_0=\frac{-\int_0^T\langle(-\Delta)^{1+2\alpha}X^N_t,\mathrm dX^N_t\rangle+\int_0^T\langle(-\Delta)^{1+2\alpha}X^N_t,P_NF_{\hat\theta^N_{1:K}}(X)\rangle\,\mathrm dt}{\int_0^T|(-\Delta)^{1+\alpha}X^N_t|_H^2\,\mathrm dt}.$$

**Statement.** Suppose the likelihood equations are solvable for large $N$, the reaction estimates $\hat\theta^N_{1:K}$ are bounded in probability, $\alpha>\gamma-d/4-1/2$, and for some $\eta,s_0>0$ and all $s_0\le s<2\gamma+1-d/2$ the solution has all moments of $\sup_t|X_t|_{H^s}$ and the nonlinearity gains $\eta$ derivatives: $|(-\Delta)^{(s-2+\eta+\epsilon)/2}F(Y)|_{C(0,T;H)}\le c\,(1+|(-\Delta)^{s/2}Y|_{C(0,T;H)})^b$. Then, as $N\to\infty$ with $T$ fixed:

1. $\hat\theta^N_0\to\theta_0$ in probability;
2. if $\eta\le1+d/2$, then $N^r(\hat\theta^N_0-\theta_0)\to0$ in probability for every $r<\eta/d$;
3. if $\eta>1+d/2$, then $N^{1/2+1/d}(\hat\theta^N_0-\theta_0)\Rightarrow\mathcal N(0,V)$ with

    $$V=\frac{2\theta_0\,(4\alpha-4\gamma+d+2)^2}{T\,d\,\Lambda^{2\alpha-2\gamma+1}\,(8\alpha-8\gamma+d+2)}.$$

For the activator–inhibitor model, the reaction estimates are bounded in probability and: in $d=1$ with $\gamma-3/4<\alpha\le\gamma$, $\hat\theta^N_0$ is consistent and asymptotically normal as in 3; in $d=2$ with $\gamma-1<\alpha<\gamma$, it is consistent with $N^r(\hat\theta^N_0-\theta_0)\to0$ for every $r<1$. So the diffusivity of the activator is identifiable in finite time from high spatial resolution alone, while the reaction parameters in general are not.

## Expansion

Inserting the dynamics into the estimator splits the error into two bias terms from the nonlinearity and a martingale term. The denominator grows like $N^{\frac2d(2\alpha-2\gamma+1)+1}$; the extra smoothness $\eta$ of $F$ makes the bias terms smaller by a factor $N^{-\eta/d}$, and the martingale term, normalized by its quadratic variation, obeys a central limit theorem. Comparing the two rates gives the three regimes.

## Sources

- Gregor Pasemann, Sven Flemming, Sergio Alonso, Carsten Beta and Wilhelm Stannat, "Diffusivity Estimation for Activator–Inhibitor Models: Theory and Application to Intracellular Dynamics of the Actin Cytoskeleton", Journal of Nonlinear Science 31 (2021), 59, <https://doi.org/10.1007/s00332-021-09714-4>; numbering as in arXiv:2005.09421: Section 2, Proposition 1 (well-posedness), Lemma 4 (growth of the denominator), Theorem 5 (consistency, rates and asymptotic normality), Proposition 6 and Theorem 7 (the linear-in-parameters and activator–inhibitor cases).
