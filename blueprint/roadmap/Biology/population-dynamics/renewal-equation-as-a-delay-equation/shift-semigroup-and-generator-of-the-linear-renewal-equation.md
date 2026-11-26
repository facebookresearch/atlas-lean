# Shift semigroup and generator of the linear renewal equation

**Setting.** In a constant environment, an individual survives to age $a$ with probability $\mathcal F(a)$ and gives birth at rate $\beta(a)$; the reproduction kernel $k(a)=\beta(a)\mathcal F(a)\ge0$ is nontrivial with compact support $[0,a_{\max}]$. The population birth rate $b$ satisfies the renewal equation
$$b(t)=\int_0^{a_{\max}}k(a)\,b(t-a)\,da,\qquad t>0,$$
with a prescribed history $b(\theta)=\phi(\theta)$ for $\theta\in[-a_{\max},0]$, $\phi\in X=L^1[-a_{\max},0]$. Writing $b=k*b+f$ on $t>0$ with the forcing $f$ from the history, the generation expansion $b=\sum_{n\ge0}k^{*n}*f$ gives a unique solution.

**Theorem (shift semigroup).** The history-to-history maps $T(t)\phi=b_t$, with $b_t(\theta)=b(t+\theta)$, form a strongly continuous semigroup of bounded linear operators on $X$. Its generator is
$$A\phi=\phi',\qquad D(A)=\Big\{\phi\in AC[-a_{\max},0]:\ \phi(0)=\int_0^{a_{\max}}k(\alpha)\,\phi(-\alpha)\,d\alpha\Big\}.$$
The rule of the renewal equation enters only through the domain, as a compatibility condition, not through the action of $A$.

**Spectrum (Euler-Lotka).** $\lambda\in\mathbb{C}$ is an eigenvalue of $A$, with eigenfunction $\theta\mapsto e^{\lambda\theta}$, exactly when $\bar k(\lambda)=\int_0^{a_{\max}}k(a)e^{-\lambda a}da=1$. Because $\bar k$ is strictly decreasing on $\mathbb{R}$ from $+\infty$ to $0$, there is a unique real root $r$, the Malthusian parameter, with $\operatorname{sign}(r)=\operatorname{sign}(R_0-1)$ for $R_0=\bar k(0)=\int\beta\mathcal F$; and there is $\varepsilon>0$ with $\operatorname{Re}\lambda\le r-\varepsilon$ for every other root.

## Expansion

$T(t)$ is translation along the extended function, so its derivative at $t=0$ is differentiation; a history lies in the domain exactly when its extension by the renewal rule is absolutely continuous, which is the matching condition at $\theta=0$. Exponentials are the functions that translation multiplies by a constant, so eigenfunctions are $e^{\lambda\theta}$ and the domain condition becomes $\bar k(\lambda)=1$. The bound $|\bar k(\lambda)|\le\bar k(\operatorname{Re}\lambda)$ shows no root has real part above $r$; Riemann-Lebesgue confines roots in a strip to a compact set, and $\cos(a\operatorname{Im}\lambda)<1$ on a set of positive $k$-measure rules out other roots on $\operatorname{Re}\lambda=r$. The resulting spectral gap yields convergence of $e^{-rt}b(t)$ and of the normalized age distribution to the stable age profile. Changing the kernel is an unbounded perturbation of $A$; sun-star calculus handles this by moving the rule into a bounded perturbation on a larger space, which also underlies the principle of linearized stability for nonlinear renewal equations.

## Sources

- Odo Diekmann, Francesca Scarabel, "Age-Structured Population Dynamics", arXiv:2506.03405 (2025), sections "The Dynamical System Perspective" (generator theorem) and "Asymptotic Large Time Behavior" (Euler-Lotka characteristic equation and spectral gap); appendix "Sun-star calculus", <https://doi.org/10.48550/arXiv.2506.03405>
