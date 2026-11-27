# Bourque distance between labeled trees with different label sets

A **labeled tree** $S$ assigns each node a nonempty set of labels (mutations), the sets partitioning the label set $L(S)$; each edge $e = (u,v)$ induces the bipartition $P(e) = \{L(u), L(v)\}$ of $L(S)$ into labels nearer $u$ and nearer $v$, and $\mathcal{P}(S)$ is the set of these. For trees $S, T$ with common labels $C = L(S) \cap L(T) \ne \emptyset$, a bipartition $\{X, L(S)\setminus X\}$ of $S$ is **similar** to a bipartition $\{C', C''\}$ of $C$ if $\{X \cap C, (L(S)\setminus X)\cap C\} = \{C', C''\}$. With $Q_S(P)$, $Q_T(P)$ the edge bipartitions of $S$, $T$ similar to $P$, the **Bourque distance** is

$$B(S,T) = |\mathcal{P}(S) \cup \mathcal{P}(T)| - \sum_{P} \min\big(|Q_S(P)|, |Q_T(P)|\big),$$

the sum over nontrivial bipartitions $P = \{C', C\setminus C'\}$ of $C$.

**Proposition.** Let $S$, $T$ have $s$ and $t$ edges. (i) If $L(S) = L(T)$ then $B(S,T) = \mathrm{RF}(S,T) \ge |s - t|$. (ii) If $L(S) \cap L(T) = \emptyset$ then $B(S,T) = \mathrm{RF}(S,T) = s + t$. (iii) If $L(S) \ne L(T)$ then $\max(s,t) \le B(S,T) \le s + t$.

**Proposition.** $B$ is a metric on labeled trees and is computable in $O(|L(S)| + |L(T)|)$ time, by adapting Day's linear-time Robinson–Foulds algorithm.

**$k$-Bourque distances.** For $k \ge 1$, let $BG_k(S,T)$ be the complete bipartite graph between the nodes of $S$ and $T$ (padded with empty nodes) weighted by the Bourque distance between the radius-$k$ neighbourhoods $C_k(u)$, $C_k(v)$. The **$k$-Bourque distance** $B_k(S,T)$ is the minimum weight of a perfect matching in $BG_k$; it is a metric for every $k$, equals $n \cdot B(S,T)$ for 1-labeled trees on $n$ nodes once $k \ge \max(\mathrm{diam}\,S, \mathrm{diam}\,T)$, and is computable in $O(\max(n,n')^3)$ time. Rooted versions use ordered (descendant, rest) bipartitions so that rerooting changes the distance.

## Depends on

- [Generalized NNI distance on node-labeled trees](generalized-nni-distance-on-node-labeled-trees.md)
- [Robinson–Foulds distance](../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

When label sets differ, every edge bipartition is distinct between the trees, so the RF distance saturates at $s + t$ and says nothing about shared structure; the Bourque correction counts, for each split of the common labels, how many edges of both trees would agree after deleting the unshared labels, and credits the smaller count. Item (iii) follows because the correction never exceeds $\min(s,t)$. Local $k$-star matching avoids the rapid saturation of global partition metrics on larger trees, which matters when comparing mutation trees inferred from different single-cell or bulk data.

## Sources

- K. Jahn, N. Beerenwinkel and L. Zhang, "The Bourque distances for mutation trees of cancers", Algorithms for Molecular Biology 16 (2021), Definitions 2–5 and Propositions 4–7, <https://doi.org/10.1186/s13015-021-00188-3>, PMCID: PMC8193869.
