# Funnel-free canonical form of a phylogenetic network

**Definitions.** A *network* on a taxon set $\mathcal{X}$ is a rooted DAG $(V, E)$ whose leaves are bijectively labeled by $\mathcal{X}$, each edge $e$ carrying a nonempty set of positive lengths $\Lambda(e) \subset \mathbb{R}_{>0}$. A *tree* is a network without reticulations (nodes of indegree $> 1$) with a single length $\lambda(e)$ per edge. A tree *contained* in $N$ has the same root, a subset of the nodes and edges of $N$, the same leaf labels, and, on each edge, one of the lengths of $N$; a tree *displayed* by $N$ is obtained from a contained tree by suppressing all indegree-1, outdegree-1 nodes (merging their two edges and adding lengths). $\mathcal{T}(N)$ is the set of displayed trees, and $N_1, N_2$ are *indistinguishable* if $\mathcal{T}(N_1) = \mathcal{T}(N_2)$.

A *funnel* is a node with indegree $> 0$ and outdegree $1$; a network is *canonical* (funnel-free) if it has no funnels, and a *canonical form* of $N$ is a canonical network indistinguishable from $N$. A *weighted path* is a directed path with one chosen length per edge; $N$ has the **NELP** (no equally long paths) property if no two distinct weighted paths with the same endpoints have the same length.

**Reduction rules.**

- **(R1) Funnel suppression.** For a funnel $v$ with in-edges $(u_1, v), \dots, (u_k, v)$ and out-edge $(v, w)$, delete $v$ and these edges and add edges $(u_i, w)$ with $\Lambda((u_i, w)) = \Lambda((u_i, v)) + \Lambda((v, w))$, where $A + B = \{a + b : a \in A, b \in B\}$.
- **(R2) Multi-edge merging.** Replace parallel edges $(u, w)$ with length sets $\Lambda'_1, \dots, \Lambda'_k$ by a single edge with lengths $\bigcup_i \Lambda'_i$.

**Theorem.** (i) Every network $N$ has a canonical form, obtained by applying (R1) and (R2) until neither applies. (ii) If $N$ has the NELP property, then $N$ has a unique canonical form among networks with the NELP property, up to isomorphism.

**Corollary 1.** Networks $N_1, N_2$ with the NELP property are indistinguishable if and only if their canonical NELP forms are isomorphic.

**Corollary 2.** A canonical network with the NELP property is the unique canonical NELP network displaying exactly the trees $\mathcal{T}(N)$; it is therefore reconstructible from its displayed trees.

## Expansion

Both rules preserve $\mathcal{T}(N)$: a funnel has a single out-edge, so every displayed tree passing through it uses that out-edge, and suppressing the funnel only merges two consecutive edges whose lengths add; merged multi-edges offer exactly the union of the alternatives. Each rule strictly decreases the number of nodes or edges, so the reduction terminates in a funnel-free network, proving (i). Uniqueness in (ii) goes through *wishbones* and *cracks* (root-to-leaf paths and path pairs sharing prefixes or suffixes): two NELP networks are isomorphic iff they contain the same wishbones and cracks, and two indistinguishable funnel-free NELP networks contain the same ones; the reduction also preserves the NELP property. NELP fails generically when edge lengths are times, since two lineages from a split to a hybridization then have equal duration, so it is a mild condition for substitution-based lengths but not for time-calibrated networks. The result says that when several distinct networks fit the same tree-wise data, only their common canonical form can be identified.

## Sources

- F. Pardi, C. Scornavacca, "Reconstructible phylogenetic networks: do not distinguish the indistinguishable", PLoS Computational Biology 11 (2015) e1004135, Results (Definitions 1–2, Theorem 1, Corollaries 1–2) and Methods (reduction rules R1–R2, Lemma 1, Propositions 1–2), <https://doi.org/10.1371/journal.pcbi.1004135>.
