# Best switching for duplication–loss reconciliation

**Setting.** A rooted phylogenetic network $N$ on label set $X$ is a rooted DAG whose root has outdegree 2, whose other internal nodes are speciation nodes (indegree 1, outdegree 2) or hybridization nodes (indegree 2, outdegree 1), and whose leaves are labelled by $X$. $N$ is level-$k$ if every biconnected component contains at most $k$ hybridization nodes. A **switching** $S$ of $N$ keeps, for every hybridization node, exactly one incoming edge (then repeatedly switches off edges whose head has only switched-off out-edges); its switched-on part is a tree. For a gene tree $G$ with $L(G)\subseteq L(N)$ and positive costs $\delta,\lambda$, $\mathrm{cost}(G,S)=\delta\,d+\lambda\,l$ is the duplication–loss cost of the LCA reconciliation of $G$ with $S$, where losses are counted only on switched-on nodes (a hybrid species inherits each gene from one parent).

**Problem (best switching).** Find a switching $S$ of $N$ minimizing $\mathrm{cost}(G,S)$.

**Theorem 1 (hardness).** The best-switching problem is NP-hard.

As in the source (Remark 1), assume that $G$ has no internal node $u$ with $|L(G_u)|=1$; otherwise first replace each such subtree $G_u$ by a leaf carrying its unique label.

**Lemma 4 (decomposition over blobs).** Let $B_1,\dots,B_p$ be the non-leaf biconnected components of $N$, and let $S$ restrict to the switching $S_i$ on the elementary network $N(B_i)$. Refine $G$ into $G_N$ by inserting artificial nodes so that each node $u$ is labelled by a biconnected component $B(u)$, and let $\mathcal G_{B_i}$ be the maximal pieces of $G_N$ labelled $B_i$; each is a binary tree or an edge. For a piece $H$, let $\beta^H_{S_i}$ be the LCA reconciliation of $H$ with $S_i$ that maps each leaf $u$ of $H$ to the leaf $r(B(u))$ of $S_i$, and let $\mathrm{dist}(x,y)$ be the number of switched-on non-leaf nodes $z$ of $S_i$ with $y<z\le x$. Define (source Definition 9) $\mathrm{cost}(H,S_i)=\mathrm{cost}(\beta^H_{S_i})$ if $H$ is a tree and $B_i=B(r(G))$; $\mathrm{cost}(H,S_i)=\mathrm{cost}(\beta^H_{S_i})+\lambda\cdot\mathrm{dist}\bigl(r(S_i),\beta^H_{S_i}(r(H))\bigr)$ if $H$ is a tree and $B_i\ne B(r(G))$; and $\mathrm{cost}(H,S_i)=\lambda\cdot\mathrm{dist}\bigl(r(S_i),r(B(u))\bigr)$ if $H$ is an edge with only leaf $u$. Then

$$\mathrm{cost}(G,S)=\sum_{i=1}^{p}\sum_{H\in\mathcal G_{B_i}}\mathrm{cost}(H,S_i),$$

so each term depends only on $H$ and the local switching $S_i$.

**Theorem 2 (FPT in the level).** If $N$ is level-$k$ with $p$ biconnected components, choosing independently for each $B_i$ the local switching minimizing $\sum_{H\in\mathcal G_{B_i}}\mathrm{cost}(H,S_i)$ yields an optimal switching, in time $O(|N|+2^k\,p\,|G|)$.

## Expansion

For hardness, since $\delta,\lambda>0$ a switching of cost 0 exists iff $G$ is displayed by $N$, so a polynomial algorithm would solve the NP-hard tree containment problem. For the algorithm, every gene node maps into a unique lowest biconnected component containing its clade; the reconciliation restricted to one component only sees the local switching, and losses on paths through a component are charged to that component. Each component has at most $2^k$ local switchings, and $|G_N|=O(p\,|G|)$, which gives the bound; biconnected components and constant-time LCA queries cost $O(|N|)$ preprocessing.

## Sources

- T.-H. To, C. Scornavacca, "Efficient algorithms for reconciling gene trees and species networks via duplication and loss events", BMC Genomics 16(Suppl 10):S6 (2015), Definitions 1–9, Problem 1, Theorem 1, Lemmas 1–4, Algorithm 1 and Theorem 2, <https://doi.org/10.1186/1471-2164-16-S10-S6>, PMCID: PMC4603766.
