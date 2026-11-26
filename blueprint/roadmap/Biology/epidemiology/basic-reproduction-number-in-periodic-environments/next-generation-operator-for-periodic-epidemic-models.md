# Next-generation operator for periodic epidemic models

**Setting.** Consider $\dot x = \mathcal{F}(t, x) - \mathcal{V}(t, x)$ with $x = (x_I, x_U)$, $x_I \in \mathbb{R}^m$ the infected compartments, all coefficients $\omega$-periodic in $t$, and a disease-free periodic solution $x^*(t) = (0, x_U^*(t))$. Let $F(t) = D_{x_I}\mathcal{F}_I(t, x^*(t)) \ge 0$ (new infections) and $V(t) = D_{x_I}\mathcal{V}_I(t, x^*(t))$ (transitions), with $-V(t)$ cooperative, and suppose the standard conditions hold: the uninfected subsystem has the globally attracting periodic state $x_U^*$, and the evolution operator $Y(t, s)$ of $\dot y = -V(t) y$ (with $Y(s,s) = I$) decays exponentially, i.e. $\rho(Y(\omega, 0)) < 1$.

**Definition.** On the Banach space $C_\omega$ of continuous $\omega$-periodic functions $\mathbb{R} \to \mathbb{R}^m$, define

$$(L\phi)(t) = \int_0^\infty Y(t, t-a)\,F(t-a)\,\phi(t-a)\, da .$$

$F(t-a)\phi(t-a)$ is the rate of new infections produced at time $t-a$ by the infected distribution $\phi$, and $Y(t, t-a)$ transports those still infected to time $t$. $L$ is positive, continuous and compact, and

$$\mathcal{R}_0 = \rho(L),$$

characterized by a nonnegative nonzero $\phi \in C_\omega$ with $L\phi = \mathcal{R}_0\phi$.

**Theorem (Wang–Zhao).** Let $\Phi_{F-V}(t)$ be the fundamental matrix of $\dot z = (F(t) - V(t)) z$. Then

$$\mathcal{R}_0 \gtreqless 1 \iff \rho\big(\Phi_{F-V}(\omega)\big) \gtreqless 1,$$

and the disease-free periodic solution $x^*(t)$ is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$. When all coefficients are constant, $\mathcal{R}_0 = \rho(FV^{-1})$.

**Global stability via Floquet comparison.** If in addition $F(t) - V(t)$ is cooperative and irreducible, then for $\mu = \omega^{-1}\ln\rho(\Phi_{F-V}(\omega))$ there is a positive $\omega$-periodic $q(t)$ with $e^{\mu t} q(t)$ solving $\dot z = (F - V)z$. If the uninfected compartments converge to $x_U^*$ and the infected subsystem is bounded above by its linearization at $x^*$ up to a perturbation $\eta M(t)$ with $\rho(\Phi_{F - V + \eta M}(\omega)) < 1$ for small $\eta > 0$, then $\mathcal{R}_0 < 1$ implies $x_I(t) \le \theta e^{\xi t} q(t) \to 0$ with $\xi < 0$, so $x^*$ is globally attractive.

## Expansion

The operator $L$ is the periodic analogue of $FV^{-1}$: for constant coefficients $Y(t, t-a) = e^{-Va}$ and $\int_0^\infty e^{-Va}F\,da = V^{-1}F$, whose spectral radius equals that of $FV^{-1}$. The equivalence with the monodromy matrix comes from the fact that $\mathcal{R}_0$ is the unique $\lambda > 0$ at which $\dot z = (F(t)/\lambda - V(t))z$ has Floquet multiplier $1$, and that multiplier is monotone in $\lambda$. Averaging coefficients over a period does not, in general, give the right threshold, which is why the operator definition matters for seasonal transmission. In computations $\mathcal{R}_0$ is obtained by finding $\lambda$ with $\rho(\Phi_{F/\lambda - V}(\omega)) = 1$ by bisection, integrating the linear system over one period.

## Sources

- P. Lou, L. Wang, X. Zhang, J. Xu, K. Wang, "Modelling Seasonal Brucellosis Epidemics in Bayingolin Mongol Autonomous Prefecture of Xinjiang, China, 2010–2014", BioMed Research International (2016) 5103718, Section 2 (equations (7)–(14), Lemma 2) and Section 3 (Lemma 3, Theorem 4 with proof (16)–(23)), <https://doi.org/10.1155/2016/5103718>.
- W. Wang, X.-Q. Zhao, "Threshold dynamics for compartmental epidemic models in periodic environments", Journal of Dynamics and Differential Equations 20 (2008) 699–717, <https://doi.org/10.1007/s10884-008-9111-8>.
