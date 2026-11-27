# Controllable sets in cancer models with co-evolving resistance

**Model.** Tumour size $n$ and mean drug-resistance trait $u$ evolve under a piecewise-constant drug dose $\alpha(t)\in A=[a_-,a_+]\subset[0,a_M]$ (bounded by the maximal tolerable dose):

$$\dot u=\varepsilon\,k(n)\,\partial_u\big(b(u,\alpha)-c(u)n\big),\qquad \dot n=n\big(b(u,\alpha)-c(u)n\big).$$

Here $\varepsilon=\mu\sigma^2$ is a small evolutionary rate (mutation fraction times mutational variance, canonical-equation scaling), $c:\mathbb R\to(0,\infty)$ is a smooth competition coefficient, and the hypotheses are:

- **H1.** $k$ is $C^1$, $k^{-1}(0)=\{0\}$ and $k'(0)>0$ (the trait evolves only while cells are present);
- **H2.** $b(u,a)=b_0(u)-a\,b_1(u)$ with $b_0,b_1$ smooth, $b_1(u)>0$ and $b_1'(u)<0$ (log-kill, with efficacy decreasing in resistance);
- **H3.** $c'(u)/c(u)>b_1'(u)/b_1(u)$ for all $u$ (fitness maxima shift toward higher resistance as the dose increases);
- **H4.** the fitness landscape $h(u,a)=b(u,a)/c(u)$ has finitely many critical points in $u$, each isolated, for every $a$, and $h(u,a)\to-\infty$ as $|u|\to\infty$ for all $a\ge0$.

The *cemetery* (cure) set is $E=\{(u,0):u\in\mathbb R\}$, a line of equilibria by H1. Let $\Gamma(x_0)$ be the reachable set from $x_0=(u_0,n_0)$ under piecewise-constant doses in $A$ and $\tilde\Gamma(x_0)$ that of the reduced system, obtained by dividing $\dot n$ by $k(n)/n$, for which $E$ is no longer invariant; the set of *curable* states is $S=\{x_0:\tilde\Gamma(x_0)\cap E\ne\emptyset\}$. By H2–H3 the equilibria with $n>0$ form the graph

$$\mathcal P=\{(x,a):\ a=a_\star(u),\ n=h_\star(u)\},\qquad h_\star(u)=h(u,a_\star(u)),$$

of a smooth function of $u$ ($a_\star(u)$ is the dose at which $u$ is a critical point of $h(\cdot,a)$); the feasible equilibria are $\mathcal P_A=\{(x,a)\in\mathcal P:a\in A\}$. Points with $a_\star'(u)>0$ are stable nodes, with $a_\star'(u)<0$ saddles, and with $a_\star'(u)=0$ isolated non-hyperbolic points. The input range is **hyperbolic** if all equilibria of the extreme vector fields $a_\pm$ are hyperbolic. A set $K$ is **controllable** if every point of $K$ can be steered to every other point of $K$ by some admissible dose schedule.

**Theorem (controllable sets).** Let $A$ be hyperbolic and $\varepsilon>0$ sufficiently small. For each connected component of feasible equilibria:
1. if both endpoints are stable nodes $(p_\pm,a_\pm)$, the curve $\Omega_1$ formed by the $a_+$-orbit from $p_-$ and the $a_-$-orbit from $p_+$ encloses a set in which the reachable set of every point is the whole enclosed set; it is thus controllable and also forward invariant (once entered it cannot be left under any schedule);
2. if both endpoints are saddles, a simple closed curve $\Omega_2$ inside their stable and unstable manifolds encloses a controllable set, which trajectories can leave;
3. if one endpoint is a stable node and the other a saddle (for the same extreme dose), a curve $\Omega_3$ built from an orbit and the saddle's invariant manifolds encloses a controllable set.

These statements hold for the reduced system; if $\Omega_j$ avoids the cure set $E$, they hold for the full system.

**Theorem (limit sets).** For hyperbolic $A$ and small $\varepsilon$, every solution starting outside the set $S$ of curable states, under any piecewise-constant dose schedule, converges in Hausdorff semi-distance to the closure of one of these controllable sets $\operatorname{enc}\Omega_j$, $j\in\{1,2,3\}$. So the controllable sets completely determine the long-term behaviour of all trajectories for which cure is unattainable.

## Expansion

The system is planar and affine in the dose. The sign of $\langle f(x,a_1)^\perp,f(x,a_2)\rangle$ is fixed on each side of the nullcline where $n$ equals the carrying-capacity level $h_\star$, so the cone of admissible velocities $f(x,A)$ always points into the region bounded by extreme-dose orbits. For small $\varepsilon$ the dynamics are slow-fast (fast ecological relaxation to $n\approx b/c$, slow drift of $u$), and the boundaries $\Omega_j$ can be built from orbits and invariant manifolds of the two extreme autonomous fields, as for perturbed singular curves. Controllability inside follows from combining extreme-dose orbits, using the angle condition to switch between them. The limit-set theorem uses a Poincaré-Bendixson-type alternative for planar differential inclusions (Filippov, Hautus): a bounded forward orbit either accumulates on the set of possible equilibria or contains a closed orbit enclosing part of it, together with structural stability of hyperbolic endpoints under small enlargement of the dose range. The practical message for adaptive therapy is that bounded doses can at best steer the tumour within these regions, never out of them.

## Sources

- F. J. Thomsen, J. L. A. Dubbeldam, "Controllability in a class of cancer therapy models with co-evolving resistance", *Discrete and Continuous Dynamical Systems - B* 32 (2026), 40–64, Section 2 (model and hypotheses), Section 3 (Definitions 1-2, Lemmas 1-3), Section 4 (Definitions 3-4, Theorems 1.1-1.3, Theorem 2) and Appendix A (Theorem A, restated Theorem 2), <https://doi.org/10.3934/dcdsb.2025121> (preprint arXiv:2503.07533).
