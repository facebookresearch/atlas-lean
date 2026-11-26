# Tree-child μ-compatibility characterizes μ-representations of tree-child networks

Let $\mathcal N$ be a rooted phylogenetic network on $[n]$ without elementary paths. The **μ-vector** of a vertex $v$ is $\mu(v)\in\mathbb N^n$ with $\mu(v)^{(i)}$ the number of directed paths from $v$ to leaf $i$; the **μ-representation** is $\mu(\mathcal N)=\{\mu(v): v\in V(\mathcal N)\}$. For tree-child networks distinct vertices have distinct μ-vectors, so $\mu(\mathcal N)$ is a set, and two tree-child networks are isomorphic iff their μ-representations coincide (Cardona, Rosselló and Valiente). The inverse question is which finite sets of vectors arise.

**Canonical order and partition.** Let $M\subseteq\mathbb N^n$ be finite with a coordinatewise maximum $\mu_\rho$. Order coordinates by $i \prec_M j$ iff $\mu_\rho^{(i)} < \mu_\rho^{(j)}$, or $\mu_\rho^{(i)}=\mu_\rho^{(j)}$ and $i<j$. Let $P_i(M)$ be the vectors of $M$ whose first non-zero coordinate in the order $\prec_M$ is $i$; the $P_i(M)$ partition $M\setminus\{0\}$.

**Definition (tree-child μ-compatible).** $M$ is tree-child μ-compatible if
1. every vector of $M$ is non-zero and the unit vectors $\delta_1,\dots,\delta_n$ lie in $M$;
2. $M$ has a coordinatewise maximum $\mu_\rho$;
3. each $P_i(M)$ is a chain $\delta_i=\mu_i^1<\mu_i^2<\dots<\mu_i^{m_i}$; write $\rho_i=\mu_i^{m_i}$;
4. for each $i$ and $j=2,\dots,m_i$ there is a non-empty $B_i^j\subseteq\{k: i\prec_M k\}$ with
$$\mu_i^j-\mu_i^{j-1}=\sum_{k\in B_i^j}\rho_k .$$

**Theorem.** A finite set $M\subseteq\mathbb N^n$ is the μ-representation of a tree-child phylogenetic network on $[n]$ without elementary paths if and only if $M$ is tree-child μ-compatible. The network is then unique up to isomorphism; it is the reconstruction digraph on vertex set $M$ with arcs $\mu_i^j\to\mu_i^{j-1}$ along each chain and bridge arcs $\mu_i^j\to\rho_k$ for $k\in B_i^j$, leaves labelled $\delta_i\mapsto i$.

## Depends on

- [Ordered tree-path decompositions characterize tree-child networks](ordered-tree-path-decomposition.md)

## Expansion

Necessity: in a tree-child network, $\mu$ is additive over children, $\mu(v)=\sum_{w\text{ child of }v}\mu(w)$, and the root dominates every vector. The number of root-to-$l_i$ paths equals the number of root-to-$r(l_i)$ paths, and $r(l_i) > r(l_j)$ forces $\mu_\rho^{(i)}<\mu_\rho^{(j)}$, so $\prec_M$ is a tree-path order. The resulting tree-path partition matches $P_i(M)$ vertex for vertex, each part is a chain ending at $\delta_i$, and the increment between consecutive vertices on a path is the sum of the μ-vectors of the bridge targets, which are the maximal vertices $\rho_k$ of later paths. Sufficiency: the reconstruction digraph built from conditions 3 and 4 is shown to be a tree-child network without elementary paths whose μ-representation is exactly $M$; uniqueness follows from the Cardona-Rosselló-Valiente isomorphism theorem. A fifth condition (every $\rho_k$ other than the root's chain top appears in some bridge sum) turns out to follow from the other four.

## Sources

- T. Fuentes, V. Moulton, K. T. Huber, J. C. Pons, "Characterization of tree-child networks in terms of mu vectors", arXiv:2609.25177 (2026), Section 2.3 (Lemma 3, Proposition 4, Theorem 5) and Section 4 (Lemma 22, Definition 27, Lemma 28, Propositions 32-34, Theorem 35), <https://doi.org/10.48550/arXiv.2609.25177>.
- G. Cardona, F. Rosselló, G. Valiente, "Comparison of tree-child phylogenetic networks", IEEE/ACM Transactions on Computational Biology and Bioinformatics 6 (2009), 552-569, <https://doi.org/10.1109/TCBB.2007.70270>.
