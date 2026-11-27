# Asymptotic counts of general and simplex time-consistent galled trees

A **galled tree** is a rooted binary phylogenetic network in which every vertex lies in at most one reticulation cycle; the cycles are **galls**, each with a top vertex $r$ and a hybrid vertex $a_r$. It is **time-consistent** (equivalently normal) if each gall's top is separated from its hybrid by at least two arcs on both paths, and **simplex** if the subtree below every hybrid vertex is a single leaf. Write $\tilde E_{n,g}$, $E_{n,g}$, $E^1_{n,g}$ for the numbers of unlabeled (non-plane) general, time-consistent and simplex time-consistent galled trees with $n$ leaves and $g$ galls, and $\tilde e_{n,g}$, $e_{n,g}$, $e^1_{n,g}$ for leaf-labeled counts. Let $\rho\approx0.40270$ and $\gamma\approx1.13003$ be the Otter constants governing the Wedderburn-Etherington numbers of unlabeled binary trees.

**Theorem (fixed number of galls, unlabeled).** For $g\ge1$, the generating function $\mathcal E^1_g(t)=\sum_n E^1_{n,g}t^n$ satisfies, as $t\to\rho^-$,

$$\mathcal E^1_g(t)\sim\frac{(4g-3)!!\,\rho^g}{(2g)!\,\gamma^{4g-1}\,(1-t/\rho)^{2g-1/2}},$$

and by singularity analysis, as $n\to\infty$,

$$E^1_{n,g}\,\rho^{-g}\sim E_{n,g}\sim\tilde E_{n,g}\sim\frac{2^{2g-1}}{(2g)!\,\gamma^{4g-1}\sqrt\pi}\,n^{2g-3/2}\rho^{-n}.$$

So for fixed $g$ general and time-consistent galled trees are asymptotically equinumerous, while the simplex restriction costs a constant factor $\rho^{g}$.

**Leaf-labeled, fixed number of reticulations $k\ge1$.**

$$e^1_{n,k}\frac{(2k)!}{k!}\sim e_{n,k}\frac{(2k)!}{2^kk!}\sim\tilde e_{n,k}\frac{(2k)!}{2^kk!}\sim\frac{2^{k-1}\sqrt2}{k!}\,n^{n+2k-1}\Big(\frac2e\Big)^n,$$

the last expression being the common asymptotic count of general, tree-child, normal and galled networks with $k$ reticulations.

**Unrestricted number of galls.** All classes follow $\frac{\delta}{2\sqrt\pi}n^{-3/2}\alpha^{-n}$ (unlabeled) or $\frac{\delta}{\sqrt2}n^{n-1}(\alpha^{-1}/e)^n$ (labeled), with different exponential rates: unlabeled $(\delta,\alpha)\approx(0.1966,0.1165)$ general, $(0.2762,0.2073)$ time-consistent, $(0.3846,0.2344)$ simplex time-consistent; labeled $(0.1894,0.1250)$, $(0.2548,0.2383)$ and $\big((9-\sqrt3)\sqrt{3(9+\sqrt3)}/117,\ (3+\sqrt3)/18\big)\approx(0.3525,0.2629)$.

**Extremal counts.** A general galled tree has at most $n-1$ galls and $\tilde E_{n,n-1}=C_{n-1}$ (Catalan), $\tilde e_{n,n-1}=(2n-2)!/(n-1)!$; a simplex time-consistent galled tree with $n$ odd has at most $(n-1)/2$ galls, and $E^1_{n,(n-1)/2}=U_{(n+1)/2}$, the number of unlabeled binary trees with $(n+1)/2$ leaves.

## Expansion

Each class has a symbolic specification: a tree is a leaf, a root with an unordered pair of subtrees ($\mathrm{MSET}_2$), or a root gall from which two non-empty sequences of vertices lead to the hybrid, each sequence vertex carrying a pendant subtree (for simplex trees the hybrid's subtree is a leaf). Marking galls gives bivariate generating functions; extracting the coefficient of $u^g$ and tracking which terms reach the highest power of $(1-t/\rho)^{-1}$ yields, by strong induction, $\mathcal E^1_g\sim\beta_g\rho^g\gamma^{1-4g}(1-t/\rho)^{1/2-2g}$ with $\beta_1=1/2$ and a convolution recurrence solved by $\beta_g=(4g-3)!!/(2g)!$. Transfer theorems with $\Gamma(2g-\tfrac12)=\sqrt\pi(4g-3)!!/2^{2g-1}$ convert this into coefficient asymptotics. For unrestricted galls, the generating function satisfies an implicit equation in the smooth implicit-function schema, giving square-root singularities whose locations differ by class; general galled trees grow fastest because a gall's top may be a parent of its hybrid, allowing up to $n-1$ galls.

## Sources

- L. Agranat-Tamir, M. Fuchs, B. Gittenberger, N. A. Rosenberg, "Combinatorial comparison of general galled trees, time-consistent galled trees, and simplex time-consistent galled trees", *Advances in Applied Mathematics* 180 (2026), 103131, Section 2 (definitions), Section 5.5 (Theorem 1, Corollary 2, Proposition 3), Sections 5.6 and 6.6 (Propositions 4-5), Section 7 (Propositions 6 and 8, Corollaries 7 and 9) and Section 8, <https://doi.org/10.1016/j.aam.2026.103131> (preprint arXiv:2601.08062).
