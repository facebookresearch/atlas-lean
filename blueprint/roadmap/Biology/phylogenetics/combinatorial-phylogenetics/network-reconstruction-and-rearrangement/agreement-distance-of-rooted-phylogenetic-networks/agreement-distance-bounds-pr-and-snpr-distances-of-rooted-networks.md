# Agreement distance bounds the PR and SNPR distances of rooted networks

**Setting.** Let $\mathcal{N}_n$ be the rooted binary phylogenetic networks on leaves $X = [n]$ (root $\rho$ of outdegree 1, tree vertices, reticulations), with $\mathcal{T}_n \subset \mathcal{N}_n$ the trees. A **prune and regraft (PR)** operation on an edge $e = (u,v)$ is one of: PR$^0$, which prunes $e$ at its tail (if $u$ is a tree vertex) or at its head (if $v$ is a reticulation) and regrafts it to a subdivision of another admissible edge; PR$^+$, which adds a new reticulation edge; and PR$^-$, which deletes a reticulation edge $(u,v)$ with $u$ a tree vertex and $v$ a reticulation. SNPR moves prune only at tails or add and delete reticulation edges. Write $d_{\mathrm{PR}}$, $d_{\mathrm{SNPR}}$ for the induced distances; on trees both restrict to the rSPR distance.

**Maximum agreement graphs.** A *pruning* of an edge $(u,v)$ at $u$ replaces it by $(\bar u, v)$ with a new unlabeled vertex $\bar u$, a *sprout*, suppressing $u$ if it becomes a degree-two vertex. Suppose $N'$ has $l \ge 0$ more reticulations than $N$. An *agreement graph* for $N, N'$ is a directed graph with components $S_1,\dots,S_k$ (agreement subgraphs) and single-edge components $E_1,\dots,E_l$ (disagreement edges) such that $G$ minus the $E_j$ embeds into $N$, and $G$ embeds into $N'$, by edge-disjoint subdivisions respecting labels; equivalently each is obtained by a sequence of prunings. A *maximum agreement graph* has the fewest sprouts. The **agreement distance** is

$$d_{\mathrm{AD}}(N, N') = s + l,$$

where $s$ is the number of sprouts in the agreement subgraphs of a maximum agreement graph.

**Theorem.**

1. $d_{\mathrm{AD}}$ is a metric on $\mathcal{N}_n$.
2. On $\mathcal{T}_n$, maximum agreement graphs are maximum agreement forests and $d_{\mathrm{AD}}$ equals the rSPR distance; hence computing $d_{\mathrm{AD}}$ is NP-hard.
3. $d_{\mathrm{AD}}(N,N') = 1$ if and only if $d_{\mathrm{PR}}(N,N') = 1$.
4. For all $N, N' \in \mathcal{N}_n$,

$$d_{\mathrm{AD}}(N,N') \le d_{\mathrm{PR}}(N,N') \le 3\,d_{\mathrm{AD}}(N,N'), \qquad d_{\mathrm{PR}} \le d_{\mathrm{SNPR}} \le 2\,d_{\mathrm{PR}},$$

and therefore $d_{\mathrm{AD}}(N,N') \le d_{\mathrm{SNPR}}(N,N') \le 6\,d_{\mathrm{AD}}(N,N')$.

Unlike the tree case, the agreement distance does not characterize $d_{\mathrm{PR}}$: there are networks with $d_{\mathrm{PR}} = 4$ but $d_{\mathrm{AD}} = 3$.

## Expansion

Each PR operation can be simulated by one pruning (a PR$^0$ prunes one edge; a PR$^\pm$ adds or removes one disagreement edge), so a PR sequence of length $m$ yields an agreement graph with at most $m$ sprouts plus disagreement edges, giving the lower bound. Conversely, given a maximum agreement graph one can choose an embedding into $N'$ in which no sprout attaches to a disagreement edge and disagreement edges attach in order; reattaching the components one at a time then costs at most three PR operations per sprout or disagreement edge, because regrafting in a network may first require temporarily moving a neighbouring edge to avoid creating cycles or parallel edges. The SNPR bound follows since a head PR$^0$ can be simulated by two SNPR moves (delete and re-add a reticulation edge).

## Sources

- Jonathan Klawitter, "The agreement distance of rooted phylogenetic networks", Discrete Mathematics & Theoretical Computer Science 21(3) (2019); arXiv:1806.05800, Section 2 (PR operations), Section 3 (Lemmas 3.1–3.3), Section 4 (Theorem 4.1, Proposition 4.2, Corollary 4.3) and Section 5 (Lemma 5.1, Theorems 5.2–5.3, Lemma 5.4, Corollary 5.5), <https://doi.org/10.48550/arXiv.1806.05800>. Published version: Discrete Mathematics & Theoretical Computer Science, Vol. 21 no. 3 , Graph Theory (May 23, 2019) dmtcs:4593, <https://doi.org/10.23638/DMTCS-21-3-19>.
