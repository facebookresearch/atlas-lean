# Singular limit of the first Lyapunov coefficient

**First Lyapunov coefficient.** For $x'=f(x;\mu)$ with a Hopf point at $x=0$, $\mu=\hat\mu$, write $f(x;\hat\mu)=Ax+\tfrac12B(x,x)+\tfrac16C(x,x,x)+O(\|x\|^4)$, let $Aq=i\omega q$, $A^{\mathsf T}p=-i\omega p$, $\langle p,q\rangle=1$. Then

$$l_1=\frac1{2\omega}\operatorname{Re}\Big[\langle p,C(q,q,\bar q)\rangle-2\langle p,B(q,A^{-1}B(q,\bar q))\rangle+\langle p,B(\bar q,(2i\omega I-A)^{-1}B(q,q))\rangle\Big],$$

and the Hopf bifurcation is supercritical if $l_1<0$ and subcritical if $l_1>0$.

**Setting.** Take a slow-fast system with two fast variables and one slow variable,

$$x'=f_1(x,y,z;\mu,\varepsilon),\qquad y'=f_2(x,y,z;\mu,\varepsilon),\qquad z'=\varepsilon g(x,y,z;\mu,\varepsilon),$$

with a non-degenerate Hopf bifurcation of frequency $\omega=O(1)$ that persists as a Hopf bifurcation of the layer problem ($\varepsilon=0$, $z$ frozen). Let $l_1^c(\varepsilon)$ be the coefficient of the full system and $\hat l_1^a$ that of the layer problem.

**Result.** In general $l_1^c(\varepsilon)-\hat l_1^a=O(1)$ as $\varepsilon\to0$: an $O(\varepsilon)$ slow equation can change the criticality, so the layer problem alone does not determine whether the onset of oscillations is sub- or supercritical. The discrepancy comes only from $\partial_xg,\ \partial_yg,\ \partial_x^2g,\ \partial_x\partial_yg,\ \partial_y^2g$ at the Hopf point; if these vanish, $l_1^c(\varepsilon)$ is an $O(\varepsilon)$ perturbation of $\hat l_1^a$ and the criticalities match. Likewise, a [quasi-steady-state elimination of fast gates](quasi-steady-state-elimination-of-fast-gating-variables.md) is not a centre-manifold reduction at a fast Hopf point and can flip criticality. A Hopf bifurcation of the slow reduced flow on a normally hyperbolic critical manifold is trouble free: $l_1(\varepsilon)$ is a regular perturbation of $l_1(0)$.

## Depends on

- [Quasi-steady-state elimination of fast gating variables](quasi-steady-state-elimination-of-fast-gating-variables.md)

## Expansion

At the Hopf point the full Jacobian has a third row of order $\varepsilon$, so its inverse has entries of order $\varepsilon^{-1}$ while the adjoint eigenvector has an $O(1)$ slow component. The cubic term changes by only $O(\varepsilon)$, but the two quadratic terms built from $A^{-1}B$ and $(2i\omega I-A)^{-1}B$ change by $O(1)$, through the linear and quadratic dependence of $g$ on the fast variables. In the Chay–Keizer pancreatic $\beta$-cell model the full five-dimensional system has a subcritical Hopf bifurcation in the applied current, while both the quasi-steady-state reduction of the calcium-channel gates and the four-dimensional layer problem give supercritical ones.

## Sources

- W. Zhang, V. Kirk, J. Sneyd, M. Wechselberger, "Changes in the criticality of Hopf bifurcations due to certain model reduction techniques in systems with multiple timescales", Journal of Mathematical Neuroscience 1 (2011) 9, Sections 3.1, 3.2, 3.2.1, 3.3, 3.3.1 and 3.4: Assumption 3, Equations (11)–(22), <https://doi.org/10.1186/2190-8567-1-9>, PMCID PMC3520151.
