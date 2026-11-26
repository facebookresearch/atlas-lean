# OLA-based optimal resolution of multifurcated trees

Let $\mathcal T=\{T_1,\dots,T_k\}$ be rooted phylogenetic trees on a common label set $L$ that may contain multifurcations (internal vertices with more than two children). A binary tree $T'$ **resolves** $T$ if contracting some edges of $T'$ yields $T$. The reticulation number of non-binary trees is the minimum over all binary resolutions $\mathcal T^*$ of $|\mathrm{MAAF}(\mathcal T^*)|-1$, where MAAF denotes a maximum acyclic agreement forest.

**Algorithm.** Fix a leaf order $\sigma$. Insert leaves $l_1,l_2,\dots$ in order into all trees simultaneously; when the parent of $l_j$ in $T^j=T|_{\{l_0,\dots,l_j\}}$ is binary the attachment point is forced, and when it is a multifurcation the algorithm chooses, among the admissible attachment points inside the partial resolution of that multifurcation, one that agrees with the attachment used by the other trees whenever possible (Lemma 5 of the source characterizes exactly which placements produce a valid resolution). The result is a set $\mathcal T'$ of binary resolutions, computed in $O(kn\cdot m\log m)$ time where $m$ is the largest multifurcation size.

**Theorem.** Let $\sigma^*$ minimize the corrected OLA distance $\hat d_\sigma$ of the trees resolved by the algorithm, and let $\mathcal T^*$ be binary resolutions of $\mathcal T$ minimizing $|\mathrm{MAAF}(\mathcal T^*)|$. Then

$$\hat d_{\sigma^*}(\mathcal T)=|\mathrm{MAAF}(\mathcal T^*)|-1=m(\mathcal T).$$

So, given an optimal leaf order, the algorithm resolves multifurcations optimally for the reticulation number.

## Depends on

- [Corrected OLA distance equals the reticulation number](corrected-ola-distance-equals-the-reticulation-number.md)

## Expansion

The lower bound is immediate: for any $\sigma$, the algorithm's output $\mathcal T'$ is a valid binary resolution, so $\hat d_\sigma(\mathcal T)=\hat d_\sigma(\mathcal T')\ge |\mathrm{MAAF}(\mathcal T')|-1\ge|\mathrm{MAAF}(\mathcal T^*)|-1$ by the binary theorem. For the upper bound, start from optimal resolutions $\mathcal T^*$ with a MAAF whose topological order is $\sigma$, and modify them one ambiguous leaf at a time into the algorithm's output. Two resolutions of the same multifurcation use the same set of internal indices, so each modification keeps a valid resolution, keeps the forest a MAAF, and keeps $\sigma$ topological for it; at the end the trees coincide with the algorithm's output, whose corrected distance is therefore at most $|\mathrm{MAAF}(\mathcal T^*)|-1$. Sorting the candidate placements within each multifurcation gives the $m\log m$ factor.

## Sources

- A. Markin, T. K. Anderson, "Ordered Leaf Attachment (OLA) vectors can identify reticulation events even in multifurcated trees", arXiv:2509.16405 (2025), Section 6 (Lemma 5, Corollary 4, Theorem 2, Lemmas 6-8, Corollaries 5-6), <https://doi.org/10.48550/arXiv.2509.16405>.
