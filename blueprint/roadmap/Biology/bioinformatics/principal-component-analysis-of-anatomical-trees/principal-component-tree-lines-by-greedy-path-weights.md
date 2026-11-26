# Principal component tree-lines are maximum-weight paths in the support tree

**Setting.** Rooted binary trees (for example the branching topology of an individual's brain arteries) are placed in correspondence so that each tree $t$ is a set of nodes of a common labeled binary tree containing the root, closed under taking parents. For a data set $T = \{t_1, \dots, t_n\}$, the *support tree* is $\mathrm{Supp}(T) = \bigcup_i t_i$, and the distance between trees is the size of the symmetric difference,

$$
d(t_1, t_2) = |t_1 \setminus t_2| + |t_2 \setminus t_1|.
$$

A **tree-line** $L = \{\ell_0, \dots, \ell_m\}$ is a sequence of trees in which $\ell_i$ is obtained from $\ell_{i-1}$ by adding one node $v_i$, each $v_{i+1}$ being a child of $v_i$; its *path* is $V_L = \ell_m \setminus \ell_0$. The projection of a tree $t$ onto $L$ is $P_L(t) = \arg\min_{\ell \in L} d(t, \ell)$, and onto a union of tree-lines with a common start it is the closest member of $\{\ell_{1,i_1} \cup \dots \cup \ell_{q,i_q}\}$. The **$k$-th principal component tree-line** is

$$
L_k^* = \arg\min_L \sum_{t_i \in T} d\big(t_i,\, P_{L_1^* \cup \dots \cup L_{k-1}^* \cup L}(t_i)\big).
$$

**Theorem.** Let $k \ge 1$ and $L_1^*, \dots, L_{k-1}^*$ be the first $k-1$ principal component tree-lines. For $v \in \mathrm{Supp}(T)$ put

$$
w_k(v) = \begin{cases} 0, & v \in V_{L_1^*} \cup \dots \cup V_{L_{k-1}^*},\\ \#\{i : v \in t_i\}, & \text{otherwise.} \end{cases}
$$

Then $L_k^*$ is the tree-line whose path maximizes $\sum_{v \in V_{L_k}} w_k(v)$ over paths in the support tree. Consequently each principal component tree-line is found by a single bottom-up pass over the support tree, in time linear in its size.

## Expansion

Two projection identities drive the proof. For one tree-line, $P_L(t) = \ell_0 \cup (t \cap V_L)$: walking down the line adds a node that lies in $t$ (reducing the distance by one) or not (increasing it by one), and the best stopping point keeps exactly the initial run of path nodes contained in $t$, which, by closure of $t$ under parents, is $t \cap V_L$. For tree-lines with a common start, the projection onto their union is the union of the individual projections. Hence minimizing the total residual distance is equivalent to maximizing $\sum_i |(V_L \cup S) \cap t_i|$ with $S$ the nodes already covered by earlier components, and every new path node contributes its data multiplicity unless it is already in $S$, which is exactly the weight $w_k$. The maximum-weight root-to-node path in a tree is computed by dynamic programming from the leaves up. Applied to brain-artery trees of 73 adults aged 18 to 72, the first-component score of the left tree (descendant correspondence) decreases with age (regression $p = 0.0025$), a location-specific version of the known age-related loss of branches.

## Sources

- B. Aydın, G. Pataki, H. Wang, E. Bullitt and J. S. Marron, *A principal component analysis for trees*, preprint arXiv:0810.0944 (2008), Section 2.2 (Definitions 2.1–2.9, Theorem 2.1) and Section 3 (Claims 3.1–3.3). <https://doi.org/10.48550/arXiv.0810.0944>
