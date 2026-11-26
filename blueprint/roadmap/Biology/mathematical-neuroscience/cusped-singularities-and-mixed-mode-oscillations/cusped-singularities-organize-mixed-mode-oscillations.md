# Cusped singularities organize mixed-mode oscillations in mutually inhibitory slow-fast systems

**Setting.** Two identical units with fast variables $x_i$ and slow variables $y_i$ inhibit each other:
$$\dot x_1=f(x_1,x_2,y_1),\quad \dot y_1=\epsilon g(x_1,y_1),\qquad \dot x_2=f(x_2,x_1,y_2),\quad \dot y_2=\epsilon g(x_2,y_2),\qquad 0<\epsilon\ll1,$$
with inhibitory coupling $\partial_{x_j}f(x_i,x_j,y_i)<0$ and exchange symmetry $(x_1,x_2,y_1,y_2)\mapsto(x_2,x_1,y_2,y_1)$. The critical manifold is $\{f(x_i,x_j,y_i)=0,\ i=1,2\}$. A symmetric point $p^*=(x^*,x^*,y^*,y^*)$ is a **non-degenerate cusped singularity** if the fold condition $f_1^*=f_2^*$ holds there ($f_1^*=\partial_{x_1}f$, $f_2^*=\partial_{x_2}f$ at $p^*$, making the antisymmetric fast direction degenerate) together with a cusp non-degeneracy condition $\Gamma\ne0$ on higher derivatives. Write $f_y^*,g_x^*,g_y^*$ for the remaining partial derivatives at $p^*$.

**Theorem.** Assume (C1) $f_2^*<0$ (inhibition), (C2) $g_y^*\le0$, (C3) $f_y^*g_x^*<0$, (C4) $\Gamma\ne0$, (C5) $g(x^*,y^*)\ne0$ (the cusp is not an equilibrium), and (C6) the slow flow crosses the cusp from the attracting sheet. Then for $0<\epsilon\ll1$:
1. the full system has a **singular Hopf bifurcation** at a nearby parameter value where $f_1^*-f_2^*=-\epsilon g_y^*$, governed by the antisymmetric block of the Jacobian, with eigenvalues $\pm i\sqrt{\epsilon|f_y^*g_x^*|}+O(\epsilon)$;
2. trajectories passing near $p^*$ make **small-amplitude oscillations** (SAOs): a center-manifold reduction gives a three-dimensional slow-fast system whose critical manifold has a cusp at the origin, and the number of SAOs is
$$n_{\mathrm{SAO}}=\Big\lfloor\frac{\lambda_2}{\lambda_1}\Big\rfloor\qquad(\lambda_2/\lambda_1\notin\mathbb N),$$
where $\lambda_1<\lambda_2<0$ are the eigenvalues of the desingularized reduced problem at the cusped singularity.

Combined with a global return mechanism, the SAOs generate **mixed-mode oscillations** (MMOs). They can show alternating patterns between the two units, unlike standard folded saddle-node MMOs.

## Expansion

The Jacobian at a symmetric point splits into a symmetric block and an antisymmetric block. With $f_1^*=f_2^*<0$ and $f_y^*g_x^*<0$, the symmetric block has negative trace $2f_1^*+\epsilon g_y^*$ and positive determinant $\approx\epsilon(2f_1^*g_y^*-f_y^*g_x^*)$, so the symmetric subspace is strongly attracting. The antisymmetric block has trace zero on the curve $f_1^*-f_2^*=-\epsilon g_y^*$ and determinant $\approx-\epsilon f_y^*g_x^*>0$, a Hopf bifurcation with $O(\sqrt\epsilon)$ frequency, which is singular. A smooth attracting four-dimensional center manifold, even in the antisymmetric coordinates, reduces the dynamics to a 3D system with a cusp-type folded singularity, to which existing blow-up results on cusped singularities give the SAO count from the eigenvalue ratio. The framework applies to the Curtu rate model of mutually inhibitory neural populations and to coupled Morris-Lecar neurons with synaptic inhibition: moving the full-system equilibrium near the cusped singularity produces SAOs around a saddle-focus, followed by large excursions.

## Sources

- M. G. Pedersen, "Cusped singularities organize mixed-mode oscillations in mutually inhibitory slow-fast systems", arXiv:2605.03606 (2026), Section 2 (Definition 1, Lemma 1, Theorem 1) and Sections 3-4 (Curtu model and coupled Morris-Lecar neurons), <https://doi.org/10.48550/arXiv.2605.03606>.
