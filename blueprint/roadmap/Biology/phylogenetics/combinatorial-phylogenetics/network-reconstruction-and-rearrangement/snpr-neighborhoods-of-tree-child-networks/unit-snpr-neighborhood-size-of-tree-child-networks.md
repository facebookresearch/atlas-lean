# Unit SNPR neighborhood size of tree-child networks

**Setting.** Networks are rooted binary phylogenetic networks with $n\ge2$ labelled leaves, a root of out-degree one and $r$ reticulations (so $2n+3r-1$ edges); $\mathcal{TC}_n$ is the class of tree-child networks. For an edge $e=(u,v)$ with $u$ not a reticulation and an edge $f$ not below $e$, the **SubNet Prune and Regraft** moves are: SNPR$^0$ (prune $e$ and regraft it to $f$, generalizing rSPR), SNPR$+$ (add an edge from a subdivision of $f$ to a subdivision of $e$) and SNPR$-$ (delete a reticulation edge and suppress its endpoints). The unit tree-child neighborhood $U^{\mathcal{TC}}(N)$ is the set of tree-child networks $N'\ne N$ reachable by one move. For an edge $e$ let $\delta(e)$ be the number of edges below it and $\delta_T(e)$ the number of tree edges below it. Structures counted in $N$: $r_1$ = reticulations whose child is a leaf; $r_2$ = paths reticulation–tree vertex–reticulation of length two; $r_3$ = configurations with edges $(x,y),(x,u),(u,w)$ where $y,w$ are reticulations; $t_3$ = triangles and $t_3^{*}$ = tree-branching triangles; $d_4$ = diamonds; $t_4$ = trapezoids with two outgoing pure tree edges. $E_R$ is the set of reticulation edges, $E_{T^*}$ the pure non-critical tree edges, $E_{PS}$ the pure tree edges with a pure tree sibling edge, and $E_{\bar t_3}$ the bottom sides of triangles.

**Rigidity.** A tree-child network has exactly one automorphism fixing its leaves, so neighbors are counted by operations modulo trivial and redundant ones.

**Theorem (SNPR$^0$ part).**

$$
\begin{aligned}
|U^{\mathcal{TC}}_{\mathrm{SNPR}^0}(N)|={}&4n^2+10nr-2n(r_2+r_3+t_3)-14n+2r^2-r(3r_2+3r_3+t_3)\\
&-11r-4r_1+4r_2+7r_3+5t_3-t_3^{*}-3d_4-t_4+14\\
&-\sum_{e\in E_{T^*}}\delta(e)-\sum_{e\in E_R}\delta_T(e)+\sum_{e\in E_{\bar t_3}}\delta_T(e).
\end{aligned}
$$

For a phylogenetic tree $T=(V,E)$ this reduces to $|U_{\mathrm{SNPR}^0}(T)|=4n^2-14n+14-\sum_{e\in E}\delta(e)$, Song's rSPR neighborhood formula.

**Proposition (SNPR$\pm$ parts).**

$$
|U^{\mathcal{TC}}_{\mathrm{SNPR}+}(N)|=4n^2-2nr-10n-2r^2+4r+6-\sum_{e\in E_{PS}}\delta_T(e),\qquad |U^{\mathcal{TC}}_{\mathrm{SNPR}-}(N)|=2r-t_3.
$$

**Theorem (full neighborhood).**

$$
\begin{aligned}
|U^{\mathcal{TC}}_{\mathrm{SNPR}}(N)|={}&8n^2+8nr-2n(r_2+r_3+t_3)-24n-r(3r_2+3r_3+t_3)-5r\\
&-4r_1+4r_2+7r_3+4t_3-t_3^{*}-3d_4-t_4+20\\
&-\sum_{e\in E_{T^*}}\delta(e)-\sum_{e\in E_R}\delta_T(e)-\sum_{e\in E_{PS}}\delta_T(e)+\sum_{e\in E_{\bar t_3}}\delta_T(e).
\end{aligned}
$$

Every parameter and sum is computable in $O(n)$ time, so the neighborhood size of a tree-child network is computable in linear time.

## Expansion

First the tree-child-respecting moves are characterized: pruning a critical edge of an $r_2$, $r_3$ or triangle structure leaves a vertex without a tree child, and regrafting below certain reticulation edges creates a reticulation with a reticulation child. Counting the allowed pairs $(e,f)$ gives a sum of descendant counts. Trivial moves and redundancy sets, distinct moves yielding the same network, arise only locally around triangles, diamonds and trapezoids and from the rSPR redundancy that three SPR moves can realize one NNI; subtracting the overcount gives the exact formula. Because tree-child networks have no nontrivial leaf-fixing automorphisms, distinct edges remain distinguishable and no further identification occurs.

## Sources

- Jonathan Klawitter, "The SNPR neighbourhood of tree-child networks", arXiv (2017), Section "Preliminaries" (automorphism proposition, SNPR operations, structures) and Section "SNPR neighbourhood of a tree-child network" (theorem on the SNPR$^0$ neighbourhood, corollary for trees, proposition on SNPR$+$ and SNPR$-$ neighbourhoods, and the theorem on the full SNPR neighbourhood), <https://doi.org/10.48550/arXiv.1707.09579> Published version: Journal of Graph Algorithms and Applications, vol. 22, no. 2, pp. 329-355 (2018), <https://doi.org/10.7155/jgaa.00472>.
