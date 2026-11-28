# Weighted SCJ small parsimony for ancestral gene adjacencies

**Setting.** Genomes are encoded by *adjacencies*: unordered pairs $\{a,b\}$ of extremities (heads or tails) of distinct markers (genes) that are neighbors on a chromosome. A set of adjacencies is *consistent*, that is free of *conflicts*, if no extremity lies in two adjacencies. Given a rooted species tree $T = (V,E)$ with $n$ leaves labeled by consistent adjacency sets $\mathcal{A}_l$ of $N$ markers, the **Small Parsimony Problem** under the Single-Cut-or-Join (SCJ) distance labels the internal nodes with consistent adjacency sets so as to minimize the total number of adjacency gains and losses along the branches. For SCJ alone this is solvable in polynomial time.

**Weighted SCJ labeling problem.** Each candidate ancestral adjacency $a$ at internal node $v$ carries a weight $w_{v,a} \in [0,1]$, for instance from ancient DNA reads or a probabilistic analysis of adjacency evolution. For a labeling $\lambda$, let $p_{v,a} = 1$ iff $a \in \lambda(v)$, and $c_{v,a} = 1$ iff $a$ is gained or lost on the branch above $v$. For $\alpha \in [0,1]$, an *optimal weighted SCJ labeling* is a conflict-free labeling minimizing

$$ D(\lambda,T) = \sum_{v,a}\Big(\alpha\,(1 - p_{v,a})\,w_{v,a} + (1 - \alpha)\,c_{v,a}\Big), $$

a convex combination of the weight of discarded ancestral adjacencies and the SCJ evolutionary cost.

**Theorem.**
1. (Hardness) The weighted SCJ labeling problem is NP-hard for every $\alpha$ with $33/34 < \alpha < 1$, via the NP-completeness of a Maximum Intersection Matching Problem.
2. (Decomposition) Build the *global adjacency graph* on all marker extremities, with an edge $\{a,b\}$ whenever some internal node has adjacency $\{a,b\}$ as a candidate. The set of optimal labelings is the Cartesian product of the optimal labelings of the instances restricted to its connected components; conflict-free components (a single edge) are solved in $O(n)$.
3. (Fixed-parameter tractability) With $D$ the maximum vertex degree and $M$ the maximum number of vertices of a conflicting component, an adaptation of the Sankoff–Rousseau dynamic program solves the problem in time $O\big(nN(1+D)^{2M}\big)$ and space $O\big(nN(1+D)^{M}\big)$. Uniform sampling of co-optimal labelings has the same bounds.

For $\alpha = 0$ the problem reduces to classical SCJ small parsimony. Increasing $\alpha$ trades evolutionary parsimony for agreement with the adjacency weights, which reduces the fragmentation of reconstructed ancestral gene orders on mammalian and *Yersinia pestis* data.

## Expansion

The SCJ cost is additive over adjacencies, so without conflicts each adjacency evolves independently, and Fitch–Sankoff on a single binary character per adjacency is optimal. Conflicts couple only adjacencies sharing an extremity, which are exactly the connected components of the global adjacency graph. Within a component, each node's label is one of at most $(1+D)^{M}$ joint states (each extremity paired with one neighbor or none), and Sankoff–Rousseau runs over these states with cost $O(r^2)$ per node for $r$ states. The problem also has an integer linear programming formulation with constraints linking $p$ and $c$ along tree edges.

## Sources

- Nina Luhmann, Manuel Lafond, Annelyse Thévenin, Aïda Ouangraoua, Roland Wittler and Cedric Chauve, "The SCJ small parsimony problem for weighted gene adjacencies (Extended version)", arXiv:1603.08819 (2016), Section 2 (Definitions 1–3, Theorems 1–2), Section 3 (Definition 4, Lemma 1, Theorems 3–4, ILP), <https://doi.org/10.48550/arXiv.1603.08819>.
