# Segregated profiles of Lotka-Volterra competition-diffusion systems

**Setting.** Consider $k \ge 2$ species with densities $u_i$ on $(-\pi, \pi)$, logistic growth rate $\mu > 0$, constant drift $c \in \mathbb{R}$, competition strength $\beta > 0$ and possibly asymmetric coefficients $\alpha_{ij} > 0$ ($i \ne j$):

$$-u_i'' - c u_i' = \mu u_i(1 - u_i) - \beta u_i \sum_{j \ne i} \alpha_{ij} u_j \ \text{ in } (-\pi,\pi), \qquad u_i(\pm\pi) = 0.$$

On an interval $(a,b)$ the *logistic solution* is the positive solution of $-w'' - c w' = \mu w(1-w)$, $w(a) = w(b) = 0$; it exists if and only if $\mu > \lambda_1(a,b) = c^2/4 + \pi^2/(b-a)^2$.

**Definition 1.1, 1.3 (segregated profile with labelling).** A labelling of $m \ge k$ intervals is a surjection $\sigma : \{1,\dots,m\} \to \{1,\dots,k\}$ with $\sigma(l) \ne \sigma(l+1)$. A segregated profile with labelling $\sigma$ consists of points $-\pi = s_0 < s_1 < \dots < s_m = \pi$ and, on each $I_l = (s_{l-1}, s_l)$, the logistic solution $V_l$, assigned to species $\sigma(l)$ and extended by zero elsewhere, subject at every interface to the **weighted flux balance**

$$\alpha_{\sigma(l+1),\sigma(l)}\, p_l = \alpha_{\sigma(l),\sigma(l+1)}\, q_l, \qquad p_l = -V_l'(s_l) > 0, \quad q_l = V_{l+1}'(s_l) > 0.$$

Definition 1.1 is the case $m = k$, $\sigma = \mathrm{id}$.

**Proposition 2.1 and Proposition 3.1 (existence threshold).** A segregated profile with a given labelling of $m$ intervals exists if and only if

$$\mu - \frac{c^2}{4} > \frac{m^2}{4},$$

and it is then unique. It is moreover nondegenerate: the only solution of the linearized logistic equations on the intervals that satisfies the linearized interface conditions is zero.

**Proposition 4.1 (radial version).** On the ball $B_R \subset \mathbb{R}^n$, $n \ge 2$, with radial shells $(s_{l-1}, s_l)$, $s_0 = 0 < \dots < s_m = R$, the same notion of profile (with $V_1'(0) = 0$) exists for a labelling of $m$ shells if and only if $\mu > j_{(n-2)/2,m}^2 / R^2$, where $j_{\nu,m}$ is the $m$-th positive zero of the Bessel function $J_\nu$; it is then unique and its radial linearization has trivial kernel.

**Proposition 2.3 (interface model).** Given slopes $p, q > 0$ and coefficients $\alpha_{12}, \alpha_{21} > 0$ with $K := \alpha_{21} p = \alpha_{12} q$, there is a unique positive solution $(a_1, a_2)$ on $\mathbb{R}$ of

$$a_1'' = \alpha_{12} a_1 a_2, \qquad a_2'' = \alpha_{21} a_1 a_2,$$

with $a_1(z) \sim -pz$, $a_2(z) \to 0$ as $z \to -\infty$ and $a_1(z) \to 0$, $a_2(z) \sim qz$ as $z \to +\infty$, normalized by $\alpha_{12} a_2(z) - \alpha_{21} a_1(z) = Kz$. It satisfies $a_1' < 0 < a_2'$.

## Expansion

Necessity of the threshold: each interval must carry a logistic solution, so each length exceeds $L_* = \pi/\sqrt{\mu - c^2/4}$, and $m$ such lengths must fit in $2\pi$. Sufficiency is a shooting argument in the interval lengths: by translation invariance the outgoing slope $A(L)$ and incoming slope $B(L)$ of the logistic solution on an interval of length $L$ are increasing functions of $L$, so the flux balance $B(L_{l+1}) = \vartheta_l A(L_l)$, $\vartheta_l = \alpha_{\sigma(l+1),\sigma(l)}/\alpha_{\sigma(l),\sigma(l+1)}$, determines every length from the first one, and continuity and monotonicity give a unique first length for which the lengths sum to $2\pi$. The flux balance is exactly the condition that the weighted difference $\alpha_{\sigma(l+1),\sigma(l)} u_{\sigma(l)} - \alpha_{\sigma(l),\sigma(l+1)} u_{\sigma(l+1)}$, in which the mutual competition terms cancel, stays $C^1$ across the interface. The interface model is the blow-up of the system at scale $\varepsilon = \beta^{-1/3}$ near an interface where both densities vanish linearly; its normalization comes from the same cancellation.

## Sources

- Z. Li, S. Terracini, "Multiple positive solutions near segregated profiles in Lotka-Volterra competition systems with asymmetric interactions" (2026), Definitions 1.1, 1.3 and 1.5, Propositions 2.1, 2.3, 3.1 and 4.1, <https://doi.org/10.48550/arXiv.2611.33975>.
