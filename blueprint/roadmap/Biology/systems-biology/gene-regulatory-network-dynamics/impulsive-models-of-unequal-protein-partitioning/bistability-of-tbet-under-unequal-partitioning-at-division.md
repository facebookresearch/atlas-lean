# Bistability of a self-activating protein under unequal partitioning at division

**Model.** The concentration $X$ of the transcription factor Tbet in a CD8 T cell obeys a positive-feedback Hill equation between divisions, and at the $k$-th division one daughter cell (the one followed) receives a fraction $1+\alpha_k$ of the mother's concentration while the other receives $1-\alpha_k$:

$$\frac{dX}{dt} = f(X) := \eta\frac{X^n}{\theta^n + X^n} - \delta X, \qquad X(\tau_k^+) = (1+\alpha_k)X(\tau_k^-),$$

with $n, \eta, \theta, \delta > 0$. This is a special case of the [scalar impulsive equation](periodic-solutions-of-a-scalar-impulsive-differential-equation.md); let $\varphi_\omega$ and $\Gamma_\omega(X_0) = X_0/\varphi_\omega(X_0) - 1$ be as there.

**Proposition (steady states without impulses).** Let $n > 1$. $f$ is convex on $[0,\Theta)$ and concave on $(\Theta,\infty)$ with $\Theta = \theta\sqrt[n]{(n-1)/(n+1)}$, and:

1. if $\eta(n-1)^{(n-1)/n} < n\delta\theta$, $X \equiv 0$ is the unique steady state and is globally asymptotically stable;
2. if equality holds, there are two steady states, $0$ (locally asymptotically stable) and $\theta\sqrt[n]{n-1}$ (semi-stable);
3. if $\eta(n-1)^{(n-1)/n} > n\delta\theta$ (hypothesis (H5)), there are three steady states $0 < X_u < X_s$ with $0$ and $X_s$ locally asymptotically stable, $X_u$ unstable, and $0 < X_u < \theta\sqrt[n]{n-1} < X_s < \eta/\delta$.

**Theorem (periodic solutions with periodic symmetric-size impulses).** Assume (H5), divisions every $\omega$ time units and constant $\alpha_k = \alpha > -1$. Then $\Gamma_\omega(X_0) \to e^{\delta\omega} - 1$ as $X_0 \to 0^+$ and as $X_0 \to \infty$, and there are $\alpha^* \in (-1,0)$ and a non-empty interval $I = [I_m, I_M] \subset [X_u, X_s)$ such that:

1. if $\alpha < \alpha^*$, $X \equiv 0$ is the only periodic solution and every solution tends to $0$;
2. at $\alpha = \alpha^*$, $X(\cdot\,;X_0,\alpha^*)$ is periodic iff $X_0 \in \{0\} \cup I$;
3. if $\alpha^* < \alpha < e^{\delta\omega} - 1$, there are exactly three periodic solutions, $0$, $X(\cdot\,;X_l,\alpha)$ and $X(\cdot\,;X_h,\alpha)$ with $\{X_l, X_h\} = \Gamma_\omega^{-1}(\{\alpha\})$, $0 < X_l < X_h$: the zero solution attracts $[0,X_l)$, the middle one is unstable, and the upper one attracts $(X_l,\infty)$; moreover $X_l \in (0,X_u)$, $X_h \in (X_s,\infty)$ if $\alpha < 0$, and $X_l \in (X_u, I_m)$, $X_h \in (I_M, X_s)$ if $\alpha > 0$;
4. if $\alpha \ge e^{\delta\omega} - 1$, $X \equiv 0$ is the only periodic solution and every positive solution tends to $+\infty$.

**Proposition (random partitioning).** If the partition coefficients vary in $[\alpha_{\min}, \alpha_{\max}]$ with $\alpha^* < \alpha_{\min} < 0 < \alpha_{\max} < e^{\delta\omega} - 1$, let $\Gamma_\omega^{-1}(\{\alpha_{\max}\}) = \{X_1, X_4\}$ and $\Gamma_\omega^{-1}(\{\alpha_{\min}\}) = \{X_2, X_3\}$; then $0 < X_1 < X_u < X_2 < X_3 < X_s < X_4$, every solution with $X_0 < X_1$ tends to $0$, and every solution with $X_0 > X_2$ is eventually trapped between the periodic solutions through $X_3$ (with $\alpha_{\min}$) and $X_4$ (with $\alpha_{\max}$), up to an arbitrarily small margin.

## Depends on

- [Periodic solutions of a scalar impulsive differential equation](periodic-solutions-of-a-scalar-impulsive-differential-equation.md)

## Expansion

The sigmoidal feedback makes $\varphi_\omega$ convex then concave (single inflection point $X_c \in (0, X_s)$), so $\varphi_\omega(x)/x$ rises to a maximum $\beta > 1$ on $I$ and falls again; equivalently $\Gamma_\omega$ decreases from $e^{\delta\omega} - 1$ to its minimum $\alpha^* = 1/\beta - 1$ on $I$ and increases back. Each level $\alpha \in (\alpha^*, e^{\delta\omega} - 1)$ is hit exactly twice, giving the low and high periodic solutions. Biologically, the daughter that repeatedly receives less Tbet ($\alpha < 0$) can cross the unstable threshold and drop to the memory-like low state, while the other is pushed to the effector-like high state; stochastic partitioning of moderate asymmetry thus generates phenotypic heterogeneity within one lineage.

## Sources

- Simon Girel and Fabien Crauste, "Existence and stability of periodic solutions of an impulsive differential equation and application to CD8 T-cell differentiation", arXiv:1803.01674 (2018), Section 5 (Propositions 8–9, Theorem 2, Lemmas 8–12) and Section 6 (Proposition 10), <https://doi.org/10.48550/arXiv.1803.01674>. Published version: Journal of Mathematical Biology, Springer Verlag (Germany), 2018, pp.1-32.
