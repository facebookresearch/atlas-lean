# Degree-preserving randomization of signed directed graphs

**Setting.** A signed causal graph is a simple directed graph $G = (V, E)$ with a sign $\pm$ on every edge, used as a model of up- and downregulation in a cell. Let $\mathcal F(G)$ be the family of signed simple digraphs on $V$ that are connected (as $G$ is) and have, at every vertex, the same positive in-degree, negative in-degree, positive out-degree and negative out-degree as $G$. A null distribution for causal-graph hypothesis scores is the uniform distribution on $\mathcal F(G)$.

**Moves.** A *same-sign edge switch* takes two edges $(a, b)$, $(c, d)$ of equal sign with no common endpoint and replaces them by $(a, d)$, $(c, b)$ with that sign. A *same-sign triangle flip* replaces a directed 3-cycle $(a, b), (b, c), (c, a)$ of equal sign by the reversed cycle $(a, c), (c, b), (b, a)$. A move is legal if the result is simple and connected; both moves preserve all four signed degree sequences.

**Statement** (Chindelevitch et al. 2012, Results, "Causal Graph Randomization"). For undirected graphs, edge switches give an ergodic chain whose stationary law is uniform on the degree-preserving family, and for directed unsigned graphs adding triangle flips restores ergodicity when connectedness is not imposed. For signed digraphs the same-sign moves do not in general reach all of $\mathcal F(G)$. Two obstructions are:

- a *strong quadrilateral*: edges $(a, b)$, $(c, d)$ of one sign together with edges $(a, d)$, $(c, b)$ of the opposite sign; swapping all four signs stays in $\mathcal F(G)$ but neither single switch is legal, since each would create a parallel edge;
- a *strong triangle*: a 3-cycle $(a, b), (b, c), (c, a)$ of one sign together with the reversed 3-cycle of the opposite sign; flipping both stays in $\mathcal F(G)$ but neither single flip is legal.

If, however, there are three same-sign edges $(a_1, a_2)$, $(b_1, b_2)$, $(c_1, c_2)$ disjoint from each other and from $\{a, b, c\}$, a strong triangle on $a, b, c$ can be flipped by a sequence of legal same-sign moves: three switches that open the triangle using the auxiliary edges, one triangle flip, three switches that close it, and two switches that restore the auxiliary edges.

## Proof sketch

The obstructions arise because the sign constraint forbids exactly the intermediate states that an unsigned chain would pass through: in a strong quadrilateral the opposite-sign edges occupy the targets of both switches. In large sparse networks auxiliary disjoint edges are abundant, so local obstructions can be bypassed, which motivates the practical sampler: repeatedly draw two edges uniformly, reject if their signs differ, perform an edge switch if they share no endpoint, or a triangle flip if they share one endpoint and lie on a directed triangle, rejecting illegal moves. Connectedness is global and costly to check, so it is verified only every $K$ steps, reverting to the last connected state on failure and adapting $K$ multiplicatively. The sampler's uniformity rests on the assumption that these moves connect $\mathcal F(G)$ in the sparse regime; the obstructions show that this is not automatic.

## Sources

- L. Chindelevitch, P.-R. Loh, A. Enayetallah, B. Berger and D. Ziemek, "Assessing statistical significance in causal graphs", BMC Bioinformatics 13 (2012), 35, Results ("Causal Graph Randomization": problem definition, challenges, Figures 5–6, algorithm), <https://doi.org/10.1186/1471-2105-13-35>, PMCID PMC3307026.
