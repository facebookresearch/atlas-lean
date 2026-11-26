# Graph criteria for stably dissipative Lotka–Volterra systems

**Setting.** Consider the $n$-species Lotka–Volterra system $\dot x_i=x_i\big(b_i+\sum_ja_{ij}x_j\big)$ on $\operatorname{int}\mathbb R^n_+$ with interior equilibrium $x^*$, i.e. $\dot x=\operatorname{diag}(x)A(x-x^*)$.

- $A$ is *Volterra–Lyapunov (semi-)stable* if $CA+A^TC$ is negative (semi-)definite for some positive diagonal $C$.
- $A$ is *stably dissipative*, $A\in\mathbb S_D$, if every sufficiently small perturbation of $A$ is Volterra–Lyapunov semi-stable.
- The graph $G(A)$ has vertex $i$ coloured black if $a_{ii}<0$ and white if $a_{ii}=0$, and an edge $[i,j]$ whenever $a_{ij}\ne0$ or $a_{ji}\ne0$; the edge is *strong* if $a_{ij}a_{ji}<0$ and *weak* if $a_{ij}a_{ji}=0$.

**Theorem.**

1. *(LaSalle reduction.)* If $A$ is Volterra–Lyapunov semi-stable, every solution converges to the largest invariant set contained in $E=\{x\in\operatorname{int}\mathbb R^n_+:(x-x^*)^T(CA+A^TC)(x-x^*)=0\}$.
2. *(One black vertex.)* If $G(A)$ has exactly one black vertex, then $A\in\mathbb S_D$ iff $G(A)$ has no cycle and every edge is strong ($a_{ij}\ne0\Rightarrow a_{ij}a_{ji}<0$ for $i\ne j$).
3. *(Several black vertices.)* Let $a_{ii}<0$ for $i\le k$ ($k\ge2$) and $a_{jj}=0$ for $j>k$, put $M=(a_{ij})_{i,j\le k}$, and let $\bar G(A)$ be $G(A)$ with all edges among black vertices removed. Then $A\in\mathbb S_D$ iff $\bar G(A)$ has no cycle and there is a positive diagonal $C=\mathrm{diag}(c_1,\dots,c_n)$ with $C_0M+M^TC_0$ negative definite ($C_0=\mathrm{diag}(c_1,\dots,c_k)$) and $c_ia_{ij}+c_ja_{ji}=0$ for $i,j>k$.

**Classification.** By these criteria the relevant interaction graphs are acyclic black/white graphs, so maximal stably dissipative graphs can be enumerated as isomorphism classes of black/white trees. Encoding each rooted tree by $\mathrm{code}(v)=[\pm\,\mathrm{size}(v),\mathrm{code}(w_1),\dots,\mathrm{code}(w_k)]$ (children sorted, sign $-$ for black), and an unrooted tree by its code at its centre (or the sorted pair of codes at a bicentre), gives a canonical form in the spirit of the Aho–Hopcroft–Ullman tree-isomorphism algorithm. Growing trees one vertex at a time and deduplicating codes, with two adjacent black vertices forbidden, lists all maximal stably dissipative graphs; the classification is computed up to $15$ vertices with colours and up to $21$ without.

## Expansion

Stable dissipativity is the robust version of the Volterra–Lyapunov condition: the Lyapunov function $V=\sum_ic_i(x_i-x_i^*-x_i^*\ln(x_i/x_i^*))$ has $\dot V=\tfrac12(x-x^*)^T(CA+A^TC)(x-x^*)\le0$, and the structure of $G(A)$ decides when this survives perturbations. The graph criteria (due to Redheffer and coauthors and to Zhao) express when such a diagonal scaling persists under all small perturbations, in terms of acyclicity of the graph and sign conditions on its edges. Classifying stably dissipative systems thus becomes a problem of enumerating coloured trees up to isomorphism, which the canonical encoding solves; for each class the LaSalle set $E$ then determines whether the interior equilibrium is globally attracting, which bears on conjectures that local stability implies global stability for prey–predator chains.

## Sources

- Yajia Du, Zhengyi Lu, Jinya Xu, Ming Yang, "A complete classification for n-species Lotka-Volterra stably dissipative systems based on a generalized AHU algorithm", arXiv:2611.00772 (2026), Section 1 (Definitions 1–3, Lemma 1), Section 2 (Definition 4, Lemmas 2–3 quoted from Redheffer and Zhao, Definition 5), Section 3 (Definitions 6–10), Section 4 (algorithm and enumeration), <https://doi.org/10.48550/arXiv.2611.00772>.
