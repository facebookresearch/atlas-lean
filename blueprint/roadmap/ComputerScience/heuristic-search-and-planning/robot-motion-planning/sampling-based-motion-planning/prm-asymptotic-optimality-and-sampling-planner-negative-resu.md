# PRM* asymptotic optimality and sampling-planner negative results (Karaman-Frazzoli)

This node collects the asymptotic-optimality and completeness results of Karaman and Frazzoli for sampling-based
planners with i.i.d. uniform samples in the configuration space $(0, 1)^d$, $d \ge 2$, for robustly feasible and robustly
optimal problems.

## Expansion

A sound expansion has separate pages for:

1. **PRM\*:** with connection radius $r_n = \gamma_{\mathrm{PRM}} (\log n/n)^{1/d}$ and
   $\gamma_{\mathrm{PRM}} > 2(1 + 1/d)^{1/d} (\mu(X_{\mathrm{free}})/\zeta_d)^{1/d}$, $\zeta_d$ the volume of the unit ball, PRM\* is
   asymptotically optimal (Theorem 34).
2. **$k$-nearest sPRM** is not asymptotically optimal for any fixed $k$ (Theorem 31, proved for a Poisson number of samples
   with mean $n$); 1-nearest sPRM is not probabilistically complete (Theorem 17).
3. **Variable-radius sPRM** with $r(n) = \gamma n^{-1/d}$ is not probabilistically complete for some $\gamma > 0$ (Theorem 20) and,
   for every $\gamma \ge 0$, not asymptotically optimal (Theorem 32).
4. **Standard PRM and RRT** are not asymptotically optimal (Theorems 29 and 33).
5. **RRT\* with radius exponent $1/d$.** Karaman and Frazzoli's Theorem 38 claims asymptotic optimality of RRT\* with
   $r_n = \gamma_{\mathrm{RRT}^*} (\log n/n)^{1/d}$; Solovey, Janson, Schmerling, Frazzoli and Pavone identified a gap in its proof,
   and the repaired statement, with exponent $1/(d+1)$, is a separate page.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Robust feasibility, probabilistic completeness and asymptotic optimality.
- Statement prerequisite: PRM, PRM*, RRT and RRT* as abstract algorithms over sample sequences.

## Related topics

- [Asymptotic optimality of RRT\* with the repaired radius (Solovey et al.)](asymptotic-optimality-of-rrt-with-the-repaired-radius.md)

## Sources

- Sampling-based Algorithms for Optimal Motion Planning — S. Karaman, E. Frazzoli, Sec. 2.1 (configuration space $(0, 1)^d$, $d \ge 2$); Sec. 4.1, Theorems 17 and 20; Sec. 4.2, Definition 24, Theorems 29, 31–34 and 38; Appendix C (proof of Theorem 34). <https://people.eecs.berkeley.edu/~pabbeel/cs287-fa15/optreadings/rrtstar.pdf>
- Revisiting the Asymptotic Optimality of RRT* — K. Solovey, L. Janson, E. Schmerling, E. Frazzoli, M. Pavone, ICRA 2020, Abstract and Sec. III: gap in KF RRT* proof. <https://par.nsf.gov/servlets/purl/10192531>
