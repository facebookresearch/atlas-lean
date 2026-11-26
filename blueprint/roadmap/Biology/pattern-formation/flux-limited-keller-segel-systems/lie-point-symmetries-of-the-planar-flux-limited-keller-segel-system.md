# Lie point symmetries of the planar flux-limited Keller–Segel system

**Setting.** The two-dimensional flux-limited Keller–Segel (FLKS) system for a cell density $u(x,y,t)$ and chemoattractant $v(x,y,t)$ is

$$u_t=\nabla\cdot\Big(\nabla u-\frac{\chi\,u\,\nabla v}{\sqrt{1+|\nabla v|^2}}\Big),\qquad v_t=\Delta v+u-v,$$

with chemotactic sensitivity $\chi>0$. The flux limiter $\nabla v/\sqrt{1+|\nabla v|^2}$ caps the chemotactic drift speed at $\chi$ and is rotation invariant, but it is not homogeneous in $\nabla v$.

**Theorem.**
1. (Symmetry algebra) The Lie algebra of point symmetries of the FLKS system is four-dimensional, spanned by

$$X_1=\partial_t,\qquad X_2=\partial_x,\qquad X_3=\partial_y,\qquad X_4=y\,\partial_x-x\,\partial_y,$$

time translation, the two spatial translations and planar rotation, with nonzero commutators $[X_2,X_4]=-X_3$ and $[X_3,X_4]=X_2$ (the Euclidean algebra of the plane extended by time translation). In particular, the scaling symmetries of the classical Keller–Segel model are broken by the flux limiter.
2. (Radial steady states) Every stationary radial solution with zero flux at the origin, $\lim_{r\to0}r\big(U_r-\chi U\,V_r/\sqrt{1+V_r^2}\big)=0$, satisfies

$$U(r)=U(r_0)\exp\Big(\chi\int_{r_0}^r\frac{V_r(s)}{\sqrt{1+V_r(s)^2}}\,ds\Big).$$

3. (Travelling waves) For one-dimensional travelling waves $u=U(\xi)$, $v=V(\xi)$, $\xi=x-ct$, with zero flux at infinity,

$$U(\xi)=U(0)\exp\Big(\chi\int_0^\xi\frac{V'(s)}{\sqrt{1+V'(s)^2}}\,ds-c\,\xi\Big).$$

Each one-dimensional subalgebra of an optimal system (stationary, translation-invariant, radial, travelling-wave and rotating-wave reductions) reduces the system to ODEs; parts 2–3 are the quadratures of the cell equation in the radial and travelling-wave reductions.

## Expansion

Applying the second prolongation of a general generator $\xi^1\partial_x+\xi^2\partial_y+\tau\partial_t+\eta^1\partial_u+\eta^2\partial_v$ to the system and splitting the determining equations with respect to derivatives of $u$ and $v$ forces $\tau$ constant, $(\xi^1,\xi^2)$ an infinitesimal Euclidean motion and $\eta^1=\eta^2=0$. Shifts of $v$ fail because the $-v$ term then requires a shift of $u$, which the chemotactic term does not allow; scalings fail because $|\nabla v|$ enters non-homogeneously. In the reductions, the cell equation is a divergence; zero flux makes the flux itself vanish, which is a first-order linear ODE for $U$ and integrates to the stated exponentials.

## Sources

- Ahmed Abbas Jaber AlFuraiji, Ghorbanali Haghighatdoost, Mustafa Bazghandi, "Lie symmetry analysis of a 2+1-dimensional flux limited Keller Segel system", arXiv:2606.25113 (2026), Section 2 (admitted Lie algebra and commutators), Section 3 (optimal system), Theorem 1 (first representation) and Theorem 3, <https://doi.org/10.48550/arXiv.2606.25113>.
