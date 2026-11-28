# Local common-reaction-path coupling converges to the split coupling

**Setting.** A stochastic reaction network on $\mathbb{Z}^d$ with reactions $k=1,\dots,R$, reaction vectors $\zeta_k$ and intensities $\lambda_k$ (for $X$) or $\tilde\lambda_k$ (for $Z$, e.g. perturbed parameters) has the random time-change representation $X(t)=X(0)+\sum_kY_k\big(\int_0^t\lambda_k(X(s))\,ds\big)\zeta_k$ with independent unit-rate Poisson processes $Y_k$. Couplings of $X$ and $Z$ reduce the variance of finite-difference sensitivity and multilevel Monte Carlo estimators.

*(i)* **Split coupling (SC):** with $r_{1k}=\lambda_k(X)\wedge\tilde\lambda_k(Z)$, $r_{2k}=\lambda_k(X)-r_{1k}$, $r_{3k}=\tilde\lambda_k(Z)-r_{1k}$,

$$X_{\rm sc}(t)=X(0)+\sum_k\Big[Y_{1k}\Big(\int_0^tr_{1k}\Big)+Y_{2k}\Big(\int_0^tr_{2k}\Big)\Big]\zeta_k,\qquad Z_{\rm sc}(t)=Z(0)+\sum_k\Big[Y_{1k}\Big(\int_0^tr_{1k}\Big)+Y_{3k}\Big(\int_0^tr_{3k}\Big)\Big]\zeta_k,$$

so the two processes share the jumps counted by $Y_{1k}$.

*(ii)* **Common reaction path (CRP):** both processes use the same $Y_k$, $X$ through $\int\lambda_k(X)$ and $Z$ through $\int\tilde\lambda_k(Z)$. Once the internal clocks drift apart the processes decouple, and estimator variance often approaches that of independent samples.

*(iii)* **Local CRP on a partition** $\pi_n=\{0=s_0<s_1<\cdots\}$: on each interval $[s_m,s_{m+1})$ fresh unit Poisson processes $Y^n_{km}$ are started and shared by $X$ and $Z$, which re-synchronizes the clocks at every $s_m$.

**Theorem.** Assume $X$ and $Z$ are non-explosive. If $\operatorname{mesh}(\pi_n)\to0$, then

$$\big(X^{\pi_n}_{\rm crp},Z^{\pi_n}_{\rm crp}\big)\Longrightarrow\big(X_{\rm sc},Z_{\rm sc}\big)$$

weakly in the product Skorokhod topology on $D_{\mathbb{R}^d}[0,\infty)^2$. More generally the same holds for any splitting of the intensities into nonnegative parts $r_{1k}+r_{2k}$ for $X$ and $r_{1k}+r_{3k}$ for $Z$: local CRP with shared clocks for these rates converges to the corresponding split-type coupling.

## Expansion

On a short interval of length $\Delta$, a shared unit Poisson process run at rates $\lambda_k(X)$ and $\tilde\lambda_k(Z)$ produces a common jump with probability about $(\lambda_k\wedge\tilde\lambda_k)\Delta$ and a jump of only the faster process with probability about $|\lambda_k-\tilde\lambda_k|\Delta$, up to $O(\Delta^2)$. These are exactly the split-coupling generator rates $\min\{\lambda_k(x),\tilde\lambda_k(z)\}$ for joint jumps and the excesses for solo jumps. Convergence of finite-dimensional distributions follows from this generator comparison, and relative compactness in Skorokhod space from the Ethier–Kurtz relative-compactness criterion, giving process-level convergence. The result explains why split coupling outperforms CRP over long horizons: it is the infinitely-frequently resynchronized version of CRP.

## Sources

- David F. Anderson and Masanori Koyama, "An asymptotic relationship between coupling methods for stochastically modeled population processes", arXiv:1403.3127 (2014), Section 3 (split, CRN and CRP couplings), Section 4 (finite-dimensional convergence, Proposition 4.7 and Theorems 4.8–4.9), <https://doi.org/10.48550/arXiv.1403.3127>.
