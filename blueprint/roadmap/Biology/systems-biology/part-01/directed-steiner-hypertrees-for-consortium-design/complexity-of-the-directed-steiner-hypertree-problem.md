# Complexity of the directed Steiner hypertree problem

**Hypergraph model.** A metabolic network is a directed hypergraph $H = (V, A)$ with compounds $V$ and reactions $A$; each hyperarc $a$ has a source set $\mathrm{src}(a)$ (substrates) and, without loss of generality, a single target. A hyperarc with $b = |\mathrm{src}(a)| > 1$ is **tentacular** with $b$ tentacles, and the **total spreadness** $k$ of $H$ is the sum of $|\mathrm{src}(a)|$ over its tentacular hyperarcs. For a consortium, the input hypergraph is the disjoint union of the networks of the worker organisms (weight $w_{\mathrm{worker}}$ per reaction), plus copies of foreign reactions inserted into each worker (weight $w_{\mathrm{other}}$), plus single-source arcs moving a compound between two workers (weight $w_{\mathrm{transition}}$). A sub-hypergraph $A' \subseteq A$ is **rooted** at $S \subseteq V$ if its hyperarcs can be ordered $a_1,\dots,a_m$ with $\mathrm{src}(a_i) \subseteq S \cup \mathrm{tgt}(\{a_1,\dots,a_{i-1}\})$ for all $i$.

**Directed Steiner hypertree problem (DSH).** Given a directed hypergraph with nonnegative hyperarc weights, sources $S$ and targets $T$, find $A' \subseteq A$ rooted at $S$ of minimum total weight with $T \subseteq \mathrm{tgt}(A')$. On ordinary digraphs a minimal solution is a forest of arborescences and DSH is the directed Steiner tree problem.

**Theorem.**

1. DSH is W[1]-hard when parameterized by any combination of $|A'|$, the weight of $A'$, $|T|$, $|S|$ and the total spreadness of $A'$.
2. DSH is NP-hard even when $|T| = 1$ and $A$ contains a single tentacular hyperarc.
3. DSH is fixed-parameter tractable in the combined parameter $|T| + k$, with $k$ the total spreadness of the input.

## Expansion

Item 1 follows from a parameterized reduction from Multi-Colour Clique in which two-tentacle hyperarcs encode the edges between colour classes; item 2 reduces the directed Steiner tree problem by adding a new target and one hyperarc from the Steiner terminals to it (proofs in the paper's supplement). The directed Steiner tree problem itself is fixed-parameter tractable in the number of targets. For tractability, fix an ordered subset $M$ of the tentacular hyperarcs used by an optimal solution; there are at most $2^k k!$ such orderings. Once $M$ is fixed, the substrates of the hyperarcs in $M$ join the targets as an extended target set $T'$ with $|T'| \le k + |T|$, and the remaining ordinary arcs of an optimal solution form a minimum-weight forest covering $T'$ (minimality removes duplicate incoming arcs and non-target leaves). That forest's weight $SH_M(T')$ obeys a subset recursion: either it is a single tree rooted at an allowed source, a directed Steiner tree instance computable in time FPT in $|T'|$, or it splits as $SH_M(Y') + SH_M(T'\setminus Y')$ over a proper subset $Y'$. Dynamic programming over the $2^{k+|T|}$ subsets, repeated for every ordering, gives the optimum $\min_M\, [\,w(M) + SH_M(T')\,]$.

## Sources

- A. Julien-Laferrière, L. Bulteau, D. Parrot, A. Marchetti-Spaccamela, L. Stougie, S. Vinga, A. Mary, M.-F. Sagot, "A combinatorial algorithm for microbial consortia synthetic design", Scientific Reports 6 (2016) 29182, Definitions 1–3, Propositions 1–2, Lemmas 1–3 and Theorems 1–2, <https://doi.org/10.1038/srep29182>, PMCID PMC4931573.
