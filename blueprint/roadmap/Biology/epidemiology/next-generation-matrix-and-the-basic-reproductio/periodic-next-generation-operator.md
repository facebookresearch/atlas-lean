# Next-generation operator in a periodic environment

**Setting.** Consider $\dot x = \mathcal{F}(t, x) - \mathcal{V}(t, x)$ with $x = (x_I, x_U)$, $x_I \in \mathbb{R}^m$ the infected compartments, all coefficients continuous and $\omega$-periodic in $t$, and a disease-free periodic solution $x^*(t) = (0, x_U^*(t))$. Let $F(t) = D_{x_I}\mathcal{F}_I(t, x^*(t))$ (new infections) and $V(t) = D_{x_I}\mathcal{V}_I(t, x^*(t))$ (transitions), and assume, as in Wang and Zhao's conditions (A1)–(A7), that $F(t) \ge 0$ entrywise, that $-V(t)$ is cooperative (nonnegative off-diagonal entries), that $x_U^*$ is linearly asymptotically stable in the disease-free subsystem, and that the evolution operator $Y(t, s)$ of $\dot y = -V(t) y$ (with $Y(s,s) = I$) satisfies $\rho(Y(\omega, 0)) < 1$, so that $\|Y(t, s)\| \le K e^{-\kappa(t - s)}$ for some $K, \kappa > 0$.

**Definition.** On the ordered Banach space $C_\omega$ of continuous $\omega$-periodic functions $\mathbb{R} \to \mathbb{R}^m$ with the maximum norm, the **next-generation operator** is

$$(L\phi)(t) = \int_0^\infty Y(t, t-a)\,F(t-a)\,\phi(t-a)\, da, \qquad \phi \in C_\omega ,$$

and the **basic reproduction number** of the periodic model is its spectral radius,

$$\mathcal{R}_0 = \rho(L).$$

The operator $L$ is positive, continuous and compact; when $\mathcal{R}_0 > 0$, the Krein–Rutman theorem makes $\mathcal{R}_0$ an eigenvalue of $L$ with a nonnegative nonzero eigenfunction $\phi \in C_\omega$.

## Depends on

- [Basic reproduction number of the next-generation matrix](r0.md)
- [Krein–Rutman theorem for $C(K)$](../../../Analysis/operator-theory/spectral-theory/krein-rutman.md)
- [The basic reproduction ratio `R₀`](../next-generation-operator-and-basic-reproduction/generation-growth.md)

## Expansion

If $\phi(s)$ is the distribution of infectious individuals introduced at time $s$, then $F(t-a)\phi(t-a)$ is the rate of new infections they produce at time $t-a$, and $Y(t, t-a)$ transports those still infected to time $t$; so $(L\phi)(t)$ is the distribution of new infections over their infectious periods. The operator generalizes the next-generation matrix: for constant coefficients $Y(t, t-a) = e^{-Va}$ and $\int_0^\infty e^{-Va}F\,da = V^{-1}F$, whose spectral radius is $\rho(FV^{-1})$. Numerically $\mathcal{R}_0$ is computed by discretizing the kernel over one period, or as the value of $\lambda$ at which $\dot z = (F(t)/\lambda - V(t))z$ has principal Floquet multiplier $1$, found by bisection.

## Sources

- W. Wang, X.-Q. Zhao, "Threshold dynamics for compartmental epidemic models in periodic environments", Journal of Dynamics and Differential Equations 20 (2008) 699–717, <https://doi.org/10.1007/s10884-008-9111-8>.
- N. Bacaër, S. Guernaoui, "The epidemic threshold of vector-borne diseases with seasonality", Journal of Mathematical Biology 53 (2006) 421–436, <https://doi.org/10.1007/s00285-006-0015-0>.
- P. Lou, L. Wang, X. Zhang, J. Xu, K. Wang, "Modelling Seasonal Brucellosis Epidemics in Bayingolin Mongol Autonomous Prefecture of Xinjiang, China, 2010–2014", BioMed Research International (2016) 5103718, Section 2 (equations (7)–(14), Lemma 2), <https://doi.org/10.1155/2016/5103718>.
- N. Nyerere, L. S. Luboobi, S. C. Mpeshe, G. M. Shirima, "Modeling the Impact of Seasonal Weather Variations on the Infectiology of Brucellosis", Computational and Mathematical Methods in Medicine 2020 (2020) 8972063, Eqs. (21)–(31), <https://doi.org/10.1155/2020/8972063> (PMC7586161).
