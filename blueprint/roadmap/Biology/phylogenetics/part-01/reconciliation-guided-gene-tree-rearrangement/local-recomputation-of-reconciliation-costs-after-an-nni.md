# Local recomputation of reconciliation costs after an NNI

**Setting.** Let $G$ be a rooted binary gene tree, $S$ a rooted dated species tree and $S'$ its subdivision (a vertex inserted on each branch at every speciation time, so that contemporaneous lineages are explicit). A reconciliation maps each gene node to a sequence of vertices of $S'$ annotated with events: speciation, duplication, horizontal transfer, loss, and the combined transfer-loss ($TL$) event. Each event type has a non-negative cost, the transfer cost $\tau$ and the loss cost $\lambda$ satisfy $\tau + \lambda > 0$, and $C(G,S') = \min_x c(\mathrm{root}(G),x)$ is the minimum reconciliation cost, where the matrix $c : V(G) \times V(S') \to \mathbb{R}_{\ge 0}$, with $c(u,x)$ the minimum cost of reconciling the subtree $G_u$ with $u$ mapped to $x$, is filled by a dynamic program in which $c(u,\cdot)$ depends only on $c(u,\cdot)$ and on $c$ at the children of $u$.

**Lemma 1 (consecutive TL events).** In a reconciliation of optimal cost, no gene node undergoes two consecutive $TL$ events.

**Lemma 2 (locality).** Let $G'$ be obtained from $G$ by a nearest-neighbour interchange (NNI) on an edge $(w,v)$, and let $c'$ be its cost matrix. For every node $z$ of $G$ that is not an ancestor of $v$, and every vertex $x$ of $S'$, $c(z,x) = c'(z,x)$.

**Theorem 1 (early stopping).** In the setting of Lemma 2, let $u$ be a strict ancestor of $w$ and $u_1$ the child of $u$ on the path to $w$. If $c(u_1,x) \le c'(u_1,x)$ for all $x \in V(S')$, then $c(u,x) \le c'(u,x)$ for all $x \in V(S')$, and consequently $C(G,S') \le C(G',S')$.

**Theorem 2.** Starting from the full matrix for $G$, a sequence of $N$ NNI evaluations can be carried out in total worst-case time $O(|S|^2\,|G| + |S|^2\,h(G)\,N)$, where $h(G)$ is the height of $G$.

## Expansion

An NNI on $(w,v)$ changes the descendant sets only of $v$'s ancestors, and every cell $c(z,x)$ depends on $z$ and its descendants alone, which gives Lemma 2. The DP recurrences are monotone in the children's cells, so if the rearranged subtree is already no cheaper at $u_1$ for every placement, no ancestor can become cheaper either, and the candidate NNI can be discarded without recomputing up to the root (Theorem 1). Building the initial matrix costs $O(|S'|\,|G|) = O(|S|^2|G|)$ because $|S'| = O(|S|^2)$, and each NNI updates only $O(h(G))$ rows of $O(|S'|)$ cells. Since the average node height of many random tree models is $O(\log |G|)$, the update is typically far cheaper than recomputing all $|G|$ rows. Lemma 1 lets the DP evaluate the $TL$ scenario of each cell after all other scenarios, from their already-computed costs.

## Sources

- T. H. Nguyen, V. Ranwez, S. Pointet, A.-M. A. Chifolleau, J.-P. Doyon, V. Berry, "Reconciliation and local gene tree rearrangement can be of mutual profit", Algorithms for Molecular Biology 8 (2013) 12, Lemmas 1–2, Theorems 1–2, <https://doi.org/10.1186/1748-7188-8-12>, PMCID PMC3871789.
