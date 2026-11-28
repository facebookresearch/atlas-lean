# Weak weighted Poincaré inequality for logarithmic potentials

**Setting.** A chemotactic density $\rho$ attracted by a fixed target obeys the Fokker–Planck equation $\partial_t\rho-\Delta\rho+\nabla\cdot(\rho\nabla H)=0$, whose ground state is $e^{H}$. In two dimensions the attractant potential of a disk-shaped target is logarithmic at infinity. The extremal (weakest) potential for a target of mass $\sim\gamma$ supported in the unit disk is

$$H(x)=\gamma\,(-\Delta)^{-1}\big(\mathbf 1_{B_1}-\mathbf 1_{B_{1/\sqrt2}}\big)(x),$$

which equals $-c\gamma\log|x|$ (plus a constant) outside $B_1$ with $c=1/4$, since the annulus $B_1\setminus B_{1/\sqrt2}$ has mass $\pi/2$ and $(-\Delta)^{-1}$ of a radial mass $m$ is $-\frac{m}{2\pi}\log|x|$ outside its support; so the weight $w=e^{H}$ decays like the power $|x|^{-\gamma/4}$ and is integrable on $\mathbb R^2$ exactly when $\gamma>8$. Convergence to $e^H$ is then algebraic rather than exponential: there is no spectral gap, and the tool is a *weak* Poincaré inequality with an extra $(1+|x|^2)$ factor in the far field. Write $\overline f$ for the $w$-weighted mean of $f$, which is defined only when $w$ is integrable.

**Theorem (two dimensions).** Let $\gamma>8$, $f\in C_0^\infty(\mathbb{R}^2)$ and $w=e^{H}$ with $H$ as above. Then

$$\int_{\mathbb{R}^2}|f-\overline f|^2\,w\,dx\le C\int_{B_1}|\nabla f|^2\,w\,dx+\frac{C}{\gamma^2}\int_{B_1^c}|\nabla f|^2\,(1+|x|^2)\,w\,dx .$$

**Theorem (power weights, any dimension).** For $v(x)=(1+|x|^2)^{-\gamma/2}$, every $d\ge2$ and all sufficiently large $\gamma$,

$$\int_{\mathbb{R}^d}|f-\overline f|^2\,v\,dx\le\frac{C(d)}{\gamma}\int_{B_1}|\nabla f|^2\,v\,dx+\frac{C(d)}{\gamma^2}\int_{B_1^c}|\nabla f|^2\,(1+|x|^2)\,v\,dx .$$

The far-field constant improves the classical Bobkov–Ledoux factor $C/\gamma$ (with the weight $(1+|x|^2)$ on the whole space) to $C/\gamma^2$, and this scaling is sharp. Both statements are special cases of a three-region inequality for radial weights (core, transition annulus, far field) with constants $C$, $C/\gamma$, $C/\gamma^2$ on the respective regions.

**Consequence for transport.** With these inequalities the weighted $L^2$ distance to equilibrium decays like $(\gamma t)^{-(\gamma-8)/8}$ after a time $t_1=C(1+\log\sigma^{-1}+\log\gamma)$, and by duality a fixed fraction of the mass of $\rho$ reaches the target region after a time of order $1/\gamma$ plus logarithmic corrections, uniformly over initial data with bounded $\|\rho_0e^{-H}\|_\infty/\|\rho_0\|_1$.

*Note on the source.* The source states the two-dimensional theorem for $\gamma>2$, but its own computation in the proof of Proposition 4.3 gives $e^H\propto|x|^{-\gamma/4}$ outside $B_1$; for $2<\gamma\le8$ the weight is not integrable and $\overline f$ is undefined, so the theorem is stated here for $\gamma>8$ (this is also the range in which the decay rate below is meaningful).

## Expansion

The proof splits $\mathbb{R}^d$ into the core $B_{r_1}$, where $w$ is essentially constant and the ordinary Poincaré inequality applies; the annulus $B_{r_2}\setminus B_{r_1}$, where $H$ is strongly decreasing with $|\nabla H|\sim\gamma$, so that integrating along rays gains one factor $1/\gamma$; and the far field, where the weight is a power $|x|^{-\gamma/4}$ and radial integration against this rapidly decaying weight gains $1/\gamma^2$ against $|x|^2|\nabla f|^2$. The three pieces $I_1,I_2,I_3$ of the variance are bounded by gradient integrals $J_1,J_2,J_3$ with absorbable cross terms ($I_2\le \frac{C}{\gamma}(J_1+J_2)+\frac14I_1$, $I_3\le\frac{C}{\gamma^2}(J_2+J_3)+\frac14I_2$). Applied to $f=\rho e^{-H}$, the inequality turns the dissipation identity for $Z(t)=\int|f-\overline f|^2e^H$ into a nonlinear differential inequality whose solution gives the algebraic decay.

## Depends on

- [$L^\infty$ bound for Fokker–Planck equations with a semiconvex drift potential](linfty-bound-for-fokker-planck-equations-with-semiconvex-drift-potential.md)

## Sources

- Alexander Kiselev, Fedor Nazarov, Lenya Ryzhik, Yao Yao, "Chemotaxis and Reactions in Biology", arXiv:2004.06441 (2020): Theorem 1.2 (two-dimensional inequality), Theorem 5.1 and Corollary 5.2 (three-region inequality), Theorem 5.4 (power weights), Theorems 6.2, 6.4 and 6.7 (convergence to equilibrium), Sections 5–6. <https://doi.org/10.48550/arXiv.2004.06441>. Published version: Journal of the European Mathematical Society 25(7) (2022), 2641–2696, <https://doi.org/10.4171/jems/1247>; locators above refer to the arXiv version.
