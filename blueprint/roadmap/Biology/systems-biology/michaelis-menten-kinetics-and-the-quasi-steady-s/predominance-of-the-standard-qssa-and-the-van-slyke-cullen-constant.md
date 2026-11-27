# Predominance of the standard QSSA and the Van Slyke-Cullen constant

**Setting.** For the Michaelis-Menten mechanism $S+E\rightleftharpoons C\to E+P$ (rate constants $k_1,k_{-1},k_2$, total enzyme $e_0$) the mass-action equations are

$$\dot s=-k_1(e_0-c)s+k_{-1}c,\qquad \dot c=k_1(e_0-c)s-(k_{-1}+k_2)c,$$

with $(s,c)(0)=(s_0,0)$. Write $K_S=k_{-1}/k_1$ (equilibrium constant), $K=k_2/k_1$ (Van Slyke-Cullen constant) and $K_M=K_S+K$ (Michaelis constant). The standard quasi-steady-state approximation (sQSSA) is $\dot s=-k_2e_0s/(K_M+s)$; its accepted validity condition is the Reich-Sel'kov condition $e_0\ll K_M$. A QSS reduction is **predominant** if it is the most accurate among the classical reductions (standard, reverse, slow-product) whose validity regions overlap.

**Trapping the slow manifold.** In the phase plane, trajectories satisfy $\frac{dc}{ds}=-\frac{e_0s-(K_M+s)c}{e_0s-(K_S+s)c}$. The region between the $c$-nullcline $c=e_0s/(K_M+s)$ and a constructed lower fence is a positively invariant, narrowing **anti-funnel** $\Gamma_0$ containing a unique slow invariant manifold $S_0^\varepsilon$. Every trajectory from the $s$-axis crosses the $c$-nullcline at some $t_{\mathrm{cross}}$, after which

$$-\frac{k_2e_0s}{K_M+s}\ \le\ \dot s\ \le\ -\frac{k_2e_0s\,(K_M+s)}{K_Me_0+(K_M+s)^2}.$$

So the sQSSA rate is accurate wherever $K_Me_0\ll(K_M+s)^2$, in particular whenever $\max\{K_M,e_0\}\ll s$, even if $e_0/K_M$ is not small, which overlaps with the reverse QSSA regime. If $e_0<8K_S$, the slow-product QSS curve also bounds a positively invariant narrowing anti-funnel containing $S_0^\varepsilon$, which every trajectory enters in finite time.

**Conclusion.** $e_0/K_M$ small controls the asymptotic accuracy of the sQSSA, but it does not make the sQSSA predominant: at low substrate, when $e_0>K$ the slow-product reduction approximates the slow manifold better. Predominance of the sQSSA requires the more restrictive condition

$$e_0\ll K=k_2/k_1 .$$

## Depends on

- [Solution of the Michaelis–Menten mass-action system](is-solution.md)
- [Michaelis constant](michaelis-constant.md)
- [Quasi-steady-state manifold](complex-rate-eq-zero-iff.md)
- [Substrate consumption at the Michaelis–Menten rate under QSSA](substrate-rate-qss.md)

## Expansion

An anti-funnel is a region between a lower fence $\alpha$ and an upper fence $\beta$ for $y'=f(x,y)$ that narrows, with the vector field pushing solutions out across both fences; the anti-funnel theorem (Hubbard-West) gives a solution trapped inside for all $x$, unique when $\partial f/\partial y$ is positive, and for the Michaelis-Menten flow this solution is the slow manifold. Fences built from the $c$-nullcline and from linearization at the stable node $(0,0)$ (eigenvalues $\lambda_\pm=\frac{k_1}2(K_M+e_0)(-1\pm\sqrt{1-4Ke_0/(K_M+e_0)^2})$) give explicit two-sided bounds on $c$ on the slow manifold, hence on $\dot s$. Comparing these bounds with the competing reduced equations in each other's validity regions shows which reduction tracks the true slow flow most closely. At small $s$, where the slow manifold leaves along the slow eigenvector, the slow-product reduction wins unless $e_0\ll K$.

## Sources

- K. Srivastava, J. Eilertsen, V. Booth, S. Schnell, "Accuracy versus predominance: reassessing the validity of the quasi-steady-state approximation", *Bulletin of Mathematical Biology* 87(6) (2025), 73, Section 3 (Definition 1, Theorem 1, Proposition 1), Section 4 (Theorem 2, Proposition 2, Section 4.2), Section 5 (Theorems 3-4, Section 5.1) and Section 6, <https://doi.org/10.1007/s11538-025-01451-z> (preprint arXiv:2501.06406).
