# Laguerre tessellation model of cells with exact volume constraints

**Static model.** Particles (cells) $i=1,\dots,N$ have positions $x_i$ in a domain $\Omega$ of unit volume and prescribed volumes $v_i$ with $V=\sum_iv_i\le1$. Given a cost function $c:\Omega\times\Omega\to[0,\infty)$, the space occupied by cell $i$ is its **Laguerre cell**

$$\mathscr L_i=\{x\in\Omega:\ c(x,x_i)-w_i\le c(x,x_j)-w_j\ \text{for all }j\},$$

where the **Kantorovich potentials** $w_1,\dots,w_N$ are chosen so that $|\mathscr L_i|=v_i$. If $V<1$, empty space is an extra particle with volume $1-V$ and zero cost. For a large class of costs (including the quadratic cost $|x-y|^2$), this partition is the unique solution of the semi-discrete optimal transport (assignment) problem

$$\mathcal T_c=\min\Big\{\sum_i\int_{\mathscr L_i}c(x,x_i)\,dx:\ (\mathscr L_i)\text{ a partition of }\Omega,\ |\mathscr L_i|=v_i\Big\},$$

whose dual variables are the $w_i$. With quadratic cost and $w_i=0$ one recovers the Voronoi diagram. Interfaces lie on $\{c(x,x_i)-w_i=c(x,x_j)-w_j\}$ (polygons for quadratic cost, curved for others), and the boundary of an isolated cell is a level set $\{c(x,x_i)=w_i-w_0\}$, so any convex shape can be encoded by the cost.

**Dynamics.** Cells move by gradient descent of the transport cost plus active and interaction forces,

$$\dot x_i=-\tau_i\nabla_{x_i}\mathcal T_c=-\tau_i\int_{\mathscr L_i}\nabla_{x_i}c(x,x_i)\,dx,$$

an **incompressibility force**. For the quadratic cost it points toward the barycenter of the Laguerre cell (a Lloyd-type relaxation) and acts as a repulsion that accounts for the actual shapes and contacts of all cells. For costs depending only on $x_i-x$, Stokes' theorem rewrites it as an internal pressure force $-\int_{\partial\mathscr L_i}c(x,x_i)\,\vec n\,d\sigma$, with pressure on each boundary element proportional to the cost, so large deformations are penalized by increasing costs. With $\tau_i\equiv1$ and no active forces or boundaries, the total momentum $\sum_i\dot x_i$ is conserved.

## Expansion

Existence and uniqueness (up to an additive constant) of potentials matching prescribed volumes is the semi-discrete optimal transport theorem: the dual objective $w\mapsto\sum_iw_iv_i+\int_\Omega\min_j(c(x,x_j)-w_j)\,dx$ is concave with gradient $v_i-|\mathscr L_i(w)|$, so its maximizer gives exactly the required volumes. The gradient of $\mathcal T_c$ with respect to a site is the integral of $\nabla_{x_i}c$ over its cell, because boundary motion does not contribute at the optimum (an envelope argument). Volume exclusion is thus imposed exactly rather than by soft penalties, as in Cellular Potts or vertex models. Simulations show orientational order of active rod-shaped cells, a fluid-solid transition controlled by deformability, deformation-driven motility, and cell sorting from surface tension differences, including in 3D.

## Sources

- A. Diez, J. Feydy, "Multicellular simulations with shape and volume constraints using optimal transport", *Science Advances* 12(28) (2026), eadv2781, Results ("Static model: Laguerre tessellation", "Dynamical model") and Materials and Methods ("Optimal Transport solver"), <https://doi.org/10.1126/sciadv.adv2781> (preprint arXiv:2402.17086).
