# Centroid-based 3D imbalance indices of rooted trees

**Setting.** A *rooted 3D tree* $\mathsf{T}=((V,E),w)$ is a rooted tree with root $\rho$ whose vertices are distinct points of $\mathbb{R}^3$ (edges are straight segments) and whose edges carry weights $w(e)>0$ (e.g. volume); $\ell(e)$ is the edge length and $w(\mathsf{T})=\sum_ew(e)$. The *centroid* $\mathcal{C}(\mathsf{T})$ is the $w$-weighted mean of the edge midpoints; for a vertex $v$, $\mathsf{T}_v$ is the pending subtree and $p(v)$ the parent.

**Node imbalance statistics** (with respect to the incoming edge $e_v=(p(v),v)$, all equal to $0$ if $\mathcal{C}(\mathsf{T}_v)=v$, e.g. at leaves):
- centroid angle $\mathcal{A}(v)=\angle\big(\mathcal{C}(\mathsf{T}_v)-v,\ v-p(v)\big)\in[0,\pi]$;
- minimal centroid angle $\alpha(v)=\min\{\mathcal{A}(v),\pi-\mathcal{A}(v)\}\in[0,\pi/2]$;
- relative centroid distance $\mu(v)=d\big(\mathcal{C}(\mathsf{T}_v),g_{v,p(v)}\big)/d\big(\mathcal{C}(\mathsf{T}_v),v\big)\in[0,1]$, with $g_{v,p(v)}$ the line through $v$ and $p(v)$ (so $\mu=\sin\alpha$);
- expanded relative centroid distance $\mathcal{M}(v)=\mu(v)$ if $\mathcal{A}(v)\le\pi/2$ and $2-\mu(v)$ otherwise, in $[0,2]$.

**Indices.** For $i\in\{\mathcal{A},\alpha,\mathcal{M},\mu\}$, the *edge imbalance* is the average of $i$ over all subdivision points of the edge, $i_{\mathsf{T}}(e_v)=\int_0^1 i_{\mathsf{T},e_v}\big(v+(p(v)-v)x\big)\,dx$, and the 3D imbalance indices $\widetilde{I}^{w}(\mathsf{T})$ and $\widetilde{I}^{\ell}(\mathsf{T})$ are the means of the edge imbalances weighted by $w(e)$ and by $\ell(e)$ respectively, giving eight indices $\widetilde{\mathcal{A}}^{w},\widetilde{\mathcal{A}}^{\ell},\widetilde{\alpha}^{w},\dots,\widetilde{\mu}^{\ell}$.

**Statements.**
1. *(Desired properties.)* All eight indices are robust to shifting, resizing and rotating or mirroring the tree, and to subdividing edges; they are proportional to weight (replacing a pending subtree by one with the same centroid and weight changes the index by the weight fraction times the change in that subtree's index); they are sensitive to linearity (elongating one edge drives the index to $0$) and to node imbalance.
2. *(Recursions.)* Weights and centroids satisfy $w(\mathsf{T})=\sum_j\big(w(e_j)+w(\mathsf{T}_j)\big)$ and $\mathcal{C}(\mathsf{T})=\frac{1}{w(\mathsf{T})}\sum_j\big(w(e_j)\tfrac{\rho+v_j}{2}+w(\mathsf{T}_j)\mathcal{C}(\mathsf{T}_j)\big)$ over the children $v_j$ of $\rho$, with closed forms for every subdivision point of an edge. Hence all node statistics are computable in $O(m+n)$ time for a tree with $n$ leaves and $m$ interior nodes, and the eight indices with at most $k$ evaluation points per edge in $O(k^2m+n)$.
3. *(Minimal trees.)* For each $i$, $\widetilde{I}^{w}(\mathsf{T})=0\iff\widetilde{I}^{\ell}(\mathsf{T})=0\iff i(v)=0$ for every interior non-root vertex $v$, i.e. every subtree centroid lies on the line of its incoming edge. Moreover $\widetilde{\mathcal{A}}=0\iff\widetilde{\mathcal{M}}=0$, $\widetilde{\alpha}=0\iff\widetilde{\mu}=0$, and $\widetilde{\mathcal{A}}=0$ implies $\widetilde{\alpha}=0$.

## Expansion

The design follows a mobile: a branch is balanced when the mass hanging below a point lies straight ahead along the direction in which that branch grew. Integrating along edges rather than evaluating only at vertices is what makes the indices independent of how a straight stem is discretized, and normalizing by length or weight makes them dimensionless and scale invariant. The node statistics differ in what they penalize: $\mathcal{A}$ and $\mathcal{M}$ distinguish centroids behind from in front of the growth direction, while $\alpha$ and $\mu$ do not, and $\mu=\sin\alpha$ punishes small deviations from straightness more strongly. Minimality follows because each edge integral is continuous and non-negative and vanishes only when it vanishes at the edge's lower endpoint.

## Sources

- Sophie J. Kersting, A. Luise Kühn and Mareike Fischer, "Measuring 3D tree imbalance of plant models using graph-theoretical approaches", Ecological Informatics 80 (2024), 102438, <https://doi.org/10.1016/j.ecoinf.2023.102438>; numbering as in arXiv:2307.14537: Section 3 (node imbalance statistics and desired properties), Section 4 (edge imbalance definition, Theorem 4.6, Proposition 4.8, Corollary 4.9, Proposition 4.10, Corollary 4.11, Theorem 4.12, Corollary 4.13).
