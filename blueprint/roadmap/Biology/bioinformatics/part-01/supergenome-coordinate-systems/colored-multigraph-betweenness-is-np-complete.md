# Colored multigraph betweenness is NP-complete

Let $\hat\Gamma = (V, E)$ be an undirected edge-coloured multigraph (for example the undirected [supergenome graph](supergenome-alignments-and-the-supergenome-graph.md), with blocks as vertices and one colour per assembly). Let $\mathcal C(\hat\Gamma)$ be the set of triples $(i, j, k)$ with $i \ne k$ such that $\{i, j\}$ and $\{j, k\}$ are edges of the same colour. The source's Definition 6 prints "the triple (i, j, k) is part of the collection 𝒞(Γ̂), iff there are edges {i,j} ∈ E and {j,k} ∈ E with color 𝒢", without $i \ne k$; read literally it puts $(i, j, i)$ in $\mathcal C(\hat\Gamma)$ for every edge $\{i, j\}$, a triple no total order satisfies, so the page makes explicit the distinctness that Definition 6 leaves implicit and that the source's Betweenness Problem and Lemma 3 presuppose. The colored multigraph betweenness problem asks whether there is a total order $<$ on $V$ such that every triple in $\mathcal C(\hat\Gamma)$ satisfies $i < j < k$ or $k < j < i$.

1. The problem is NP-complete.
2. If the directed supergenome graph $\Gamma$ is acyclic, any topological sorting of $\Gamma$ solves it.
3. Call $v, w$ a mini-cycle if both $(v, w)$ and $(w, v)$ are edges of $\Gamma$, and two mini-cycles connected if they share a vertex. The maximal connected sets of mini-cycles (mini-cycle complexes) form a unique partition of all mini-cycles, and distinct complexes are vertex- and edge-disjoint.

## Depends on

- [Supergenome alignments and the supergenome graph](supergenome-alignments-and-the-supergenome-graph.md)

## Expansion

Membership in NP is immediate. Hardness follows from the classical Betweenness problem (Opatrny): every finite set of triples arises as $\mathcal C(\hat\Gamma)$ by giving each triple its own colour and two edges, so a total order of $\hat\Gamma$ is exactly a betweenness ordering. In a DAG every same-colour triple is a directed path $i \to j \to k$ or its reverse, and a topological order preserves all directed paths. Real alignments contain cycles, mostly short ones from local rearrangements; mini-cycle complexes are the connected components of an auxiliary graph whose vertices are mini-cycles, and they are resolved independently by dropping the less supported edge direction before topological sorting, which gives a practical heuristic.

## Sources

- F. Gärtner, C. Höner zu Siederdissen, L. Müller and P. F. Stadler, "Coordinate systems for supergenomes", Algorithms for Molecular Biology 13 (2018) 15, <https://doi.org/10.1186/s13015-018-0133-4>, PMCID PMC6151955. Definitions 6–8 and Lemmas 2–4.
