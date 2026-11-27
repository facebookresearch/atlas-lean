# Common trees explaining orthology and xenology maps

**Setting.** Let $L$ be a finite set of genes and $\mathcal L=\{(x,y):x,y\in L,\ x\neq y\}$. A rooted phylogenetic tree $T$ on $L$ with inner-vertex labels $t:V^0(T)\to M$ *explains* $\delta:\mathcal L\to M$ if $t(\mathrm{lca}_T(x,y))=\delta(x,y)$ for all $x\neq y$. Such $\delta$ is exactly a *symbolic ultrametric*: it is symmetric, has no induced "$P_4$" pattern $\delta(x,y)=\delta(y,u)=\delta(u,v)\neq\delta(y,v)=\delta(x,v)=\delta(x,u)$, and takes at most two values on every triangle. It then has a unique least-resolved (discriminating) tree $(T_\delta,t_\delta)$. With $M=\{\text{speciation},\text{duplication}\}$, $\delta$ encodes orthology.

An edge labeling $\lambda:E(T)\to 2^N$ *explains* $\varepsilon:\mathcal L\to 2^N$ if, for each $k\in N$, $k\in\varepsilon(x,y)$ exactly when some edge on the path from $\mathrm{lca}_T(x,y)$ to $y$ carries $k$. Maps of this form are *Fitch maps*; they record directed horizontal-transfer (xenology) events and have a unique least-resolved tree $(T_\varepsilon,\lambda_\varepsilon)$. Write $\mathcal H(T)$ for the hierarchy of clusters of $T$. A pair $(\delta,\varepsilon)$ is *tree-like* if a single tree $(T,t,\lambda)$ explains both maps.

**Theorem.**

1. *(Refinements.)* $(T,t)$ explains $\delta$ for some $t$ iff $T$ refines $T_\delta$, and then $t$ is unique. $(T,\lambda)$ explains $\varepsilon$ for some $\lambda$ iff $T$ refines $T_\varepsilon$, and then there is a unique labeling minimizing $\sum_e|\lambda(e)|$.
2. *(Characterization.)* $(\delta,\varepsilon)$ is tree-like iff (i) $\delta$ is a symbolic ultrametric, (ii) $\varepsilon$ is a Fitch map, and (iii) $\mathcal H^*=\mathcal H(T_\delta)\cup\mathcal H(T_\varepsilon)$ is a hierarchy. In that case there is a unique least-resolved tree $(T^*,t^*,\lambda^*)$ explaining both maps, with $\mathcal H(T^*)=\mathcal H^*$, $t^*$ induced by $t_\delta$ and the minimum-weight $\lambda^*$ induced by $\lambda_\varepsilon$.
3. *(Algorithm.)* Whether $(\delta,\varepsilon)$ is tree-like can be decided, and $(T^*,t^*,\lambda^*)$ constructed, in $O(|L|^2|N|)$ time.
4. *(Biological constraints.)* Suppose a transfer must leave a non-transferred child at every inner vertex (condition (C)), and vertices with labels in $M_\emptyset\subseteq M$ carry no transfer on their child edges (condition (C1)). Then $(\delta,\varepsilon)$ is explained by a tree satisfying both iff it is tree-like and its least-resolved tree $(T^*,t^*,\lambda^*)$ satisfies (C) and (C1).

## Proof sketch

Both kinds of data are explained by refinements of their own least-resolved trees, so a common explanation exists exactly when the two cluster hierarchies are compatible, which means their union is again a hierarchy. Refining a tree never destroys the explanation of either map: vertex labels pass to the new lca's, and edge labels can be placed on any edge of the original path. Taking the coarsest common refinement gives uniqueness. Conditions (C) and (C1) are inherited by refinements in the right direction, so it is enough to check them on $T^*$. The complexity comes from building $T_\delta$ and $T_\varepsilon$ and testing pairwise compatibility of clusters.

## Sources

- Marc Hellmuth, Mira Michel, Nikolai N. Nøjgaard, David Schaller and Peter F. Stadler, "Combining Orthology and Xenology Data in a Common Phylogenetic Tree", in *Lecture Notes in Computer Science*, Springer International Publishing, 2021, 53–64, <https://doi.org/10.1007/978-3-030-91814-9_5>. Preprint version: arXiv:2107.01893 (2021), Lemmas 3 and 5 with Corollary 2 (refinements), Theorem 1 (characterization and unique least-resolved tree), Theorem 2 (complexity), Theorem 3 (constraints (C) and (C1)), <https://doi.org/10.48550/arXiv.2107.01893>.
