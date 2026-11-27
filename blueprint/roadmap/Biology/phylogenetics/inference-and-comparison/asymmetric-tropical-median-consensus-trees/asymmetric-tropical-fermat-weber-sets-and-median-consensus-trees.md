# Asymmetric tropical Fermat–Weber sets and median consensus trees

**Setting.** On the tropical projective torus $\mathbb R^n/\mathbb R\mathbf 1$, the *asymmetric tropical distance* is

$$d_\triangle(a,b)=\sum_{i\in[n]}(b_i-a_i)-n\min_{i\in[n]}(b_i-a_i)=\sum_{i}(b_i-a_i)+n\max_i(a_i-b_i),$$

which is well defined modulo $\mathbb R\mathbf 1$, non-negative, and in general not symmetric. Its symmetrization is $n$ times the usual symmetric tropical distance. For sites $V=\{v_1,\dots,v_m\}$, the *Fermat–Weber set* $\mathrm{FW}(V)$ is the set of minimizers of $x\mapsto\sum_{i}d_\triangle(v_i,x)$. Restricted to the normalizing hyperplane $\mathcal H$ this sum equals $n\sum_i\max_j(v_{ij}-x_j)$. A point $u$ *evenly splits* $V$ if, for every $J\subseteq[n]$, the union $S_J(u)$ of the closed sectors with apex $u$ indexed by $J$ contains at least $m|J|/n$ sites.

**Theorem.**

1. $\mathrm{FW}(V)$ is the central cell of the covector decomposition induced by $V$. It is a bounded polytrope, convex both classically and tropically, and it lies in the max-tropical convex hull of $V$.
2. $\dim\mathrm{FW}(V)\le\gcd(m,n)-1$; in particular the Fermat–Weber point is unique when $m$ and $n$ are coprime.
3. $u\in\mathrm{FW}(V)$ iff $u$ evenly splits $V$. The linear programming dual of the Fermat–Weber problem is a transportation problem with supplies $n$ at the $m$ sites and demands $m$ at the $n$ coordinates, and the support graph of an optimal dual solution is the covector of the Fermat–Weber point it determines. Consequently, for $m\ge n$ one Fermat–Weber point can be computed in $O(n^2m\log^2m)$ time, and the facets and tropical vertices of $\mathrm{FW}(V)$ can be found in strongly polynomial time.
4. *(Consensus trees.)* Let $V$ be a set of $m$ equidistant (ultrametric) trees on $n$ leaves, viewed in $\mathbb R^{\binom n2}$ through their distance vectors. Then $\mathrm{FW}(V)$ consists of equidistant trees that all share one topology, and $\dim\mathrm{FW}(V)\le\min\big(n-1,\gcd(m,\binom n2)\big)-1$. The resulting *tropical median consensus tree* is Pareto and co-Pareto on rooted triplets: every triplet common to all input trees appears in the consensus, and every triplet of the consensus appears in some input tree.

## Proof sketch

The objective $\sum_i\max_j(v_{ij}-x_j)$ is a minimax linear program. Its dual asks for a transportation plan that ships each site's mass to the coordinates where it attains the maximum, and complementary slackness turns optimality into the balancing condition "evenly splits": every group of $|J|$ sectors must hold its proportional share $m|J|/n$ of sites. Integrality of the transportation polytope explains the $\gcd(m,n)$ bound on dimension. Tree space for equidistant trees is the Bergman fan of the graphic matroid of $K_n$, and it is tropically convex. So the Fermat–Weber set of trees stays inside tree space, and tropical convexity rules out topology changes within it. This makes the median a well-defined consensus method that is regular in the sense of Bryant–Francis–Steel.

## Sources

- Andrei Comăneci and Michael Joswig, "Tropical medians by transportation", *Mathematical Programming* 205 (2024), 813–839, <https://doi.org/10.1007/s10107-023-01996-8>. Preprint version: arXiv:2205.00036 (2022), Section 3 (definition of $d_\triangle$, Theorem 1 on the covector cell, Theorem 2 on dimension), Section 4 (Theorem 3 transportation duality, Corollaries 4–5 complexity), Section 5 (Theorem 6 and Corollary 7 on equidistant trees, Pareto and co-Pareto properties), <https://doi.org/10.48550/arXiv.2205.00036>.
