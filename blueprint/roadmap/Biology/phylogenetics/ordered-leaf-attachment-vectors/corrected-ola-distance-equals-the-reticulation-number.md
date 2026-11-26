# Corrected OLA distance equals the reticulation number

**OLA vectors.** Let $T$ be a rooted binary phylogenetic tree on leaves $L\setminus\{\rho\}$ (planted at an extra root label $\rho$) and fix a bijection $\sigma$ from leaves to $\{0,\dots,n-1\}$, $\sigma(l_i)=i$. For a vertex $v$ let $\mu(v)=\min\{\sigma(l): l\in L(T_v)\}$, and give each internal vertex $v$ with children $v_{(1)},v_{(2)}$ the index $\sigma(v)=-\max\{\mu(v_{(1)}),\mu(v_{(2)})\}$. With $T^i=T|_{\{l_0,\dots,l_i\}}$ and $v_i$ the sibling of $l_i$ in $T^i$, the **ordered leaf attachment vector** is
$$\mathrm{OLA}(T,\sigma)_i=\sigma(v_i),\qquad i=1,\dots,n-1 .$$
It satisfies $-(i-1)\le \mathrm{OLA}(T,\sigma)_i\le i-1$, and every integer vector with these bounds encodes exactly one tree (a bijection with the $(2n-3)!!$ rooted binary trees), with linear-time encoding and decoding.

**Corrected OLA distance.** For a set $\mathcal T$ of $k\ge 2$ trees on the same leaves, build a mismatch set $M\subseteq\{1,\dots,n-1\}$ by scanning $i=1,\dots,n-1$ and adding $i$ if either two trees disagree at coordinate $i$, or all trees agree with $\mathrm{OLA}(T,\sigma)_i=-j$ for some $j\in M$ already (leaf $l_i$ sits on top of an already mismatched attachment). Set $\hat d_\sigma(\mathcal T)=|M|$; it is computable in $O(kn)$ time. (The plain Hamming distance can undercount.)

**Agreement forests.** An agreement forest $\mathcal F$ for $\mathcal T$ is a partition of the leaves into label sets whose restricted trees are identical in every $T\in\mathcal T$ and span vertex-disjoint subtrees of each $T$; it is **acyclic** if its inheritance graph (an arc $C_i\to C_j$ when some tree has a path from the root of $T(L(C_i))$ to that of $T(L(C_j))$) has no directed cycle. A maximum acyclic agreement forest (MAAF) has the fewest components, and the **reticulation number** is $m(\mathcal T)=|\mathrm{MAAF}(\mathcal T)|-1$ (for two trees, the hybridization number).

**Theorem.** For $k>1$ binary trees on a common label set, with $\sigma^*=\arg\min_\sigma \hat d_\sigma(\mathcal T)$,
$$\hat d_{\sigma^*}(\mathcal T)=m(\mathcal T)=|\mathrm{MAAF}(\mathcal T)|-1 .$$
Moreover, for every $\sigma$, $\hat d_\sigma(\mathcal T)\ge m(\mathcal T)$, and a MAAF is read off from the mismatch structure of optimal OLA vectors.

## Expansion

Upper bound: take a MAAF and a leaf order following a topological order of its acyclic inheritance graph, listing each component's leaves consecutively. A leaf that is not the first of its component attaches to the same indexed vertex in every tree, because each component is embedded identically in all trees and its nodes are indexed by its own leaves; so only the first leaves of the non-root components can mismatch, and the correction never fires spuriously, giving $\hat d_\sigma=d_\sigma\le |\mathcal F|-1$. Lower bound: for any $\sigma$, the leaves between consecutive corrected mismatches form groups whose restrictions are node-disjoint and identically indexed in every tree, hence an agreement forest with $\hat d_\sigma+1$ components, and the order $\sigma$ itself rules out cycles (no component's subtree contains an earlier leaf of a later group). Since optimizing $\sigma$ is as hard as the NP-hard MAAF problem, the practical content is a cheap randomized heuristic: sample leaf orders, keep the minimum $\hat d_\sigma$, and reconstruct a network. In microbial data a sampling-date order is a natural candidate.

## Sources

- A. Markin, T. K. Anderson, "Ordered Leaf Attachment (OLA) vectors can identify reticulation events even in multifurcated trees", arXiv:2509.16405 (2025), Sections 2-4 (definition of OLA vectors and corrected distance, Theorem 1, Lemmas 1-4, Corollaries 1-3), <https://doi.org/10.48550/arXiv.2509.16405>.
