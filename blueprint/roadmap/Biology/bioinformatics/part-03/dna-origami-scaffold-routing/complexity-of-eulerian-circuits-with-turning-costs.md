# Complexity of Eulerian circuits with turning costs

**Setting.** In DNA origami a single scaffold strand is routed through a target structure and pinned by staple strands. When the target is a graph-like wireframe (a $1$-complex), a scaffold route that traverses every edge once is an Eulerian circuit, and the geometric cost of how the strand turns at each vertex matters. Formally, let $G$ be an Eulerian graph (connected, all degrees even). A *pairing* at a vertex $v$ is an unordered pair $\{(v,e),(v,f)\}$ of distinct half-edges at $v$; each pairing carries a non-negative rational *turning cost* $w_v(e,f)$. An Eulerian circuit $C$ determines a perfect matching $T_C(v)$ of the half-edges at each $v$ (consecutive edges through $v$), and its cost is

$$
w(C)=\sum_{v\in V(G)}w(T_C(v)).
$$

**Problem.** Find an Eulerian circuit of minimum cost; decision version: is there one with $w(C)\le c$?

**Theorem.**

1. *(Hardness.)* From a 3-SAT instance $I$ with $n$ literals and $r$ clauses one can build, in $O(nr^2)$ time, an Eulerian graph $G_I$ with turning costs in $\{0,1\}$ such that $I$ is satisfiable iff $G_I$ has a zero-cost Eulerian circuit. Hence the decision problem is NP-complete and the optimization problem is NP-hard, already for $0/1$ costs.
2. *(Bounded degree.)* The problem remains NP-hard on graphs of maximum degree $8$.
3. *(Reduction to TSP.)* Subdivide every edge of $G$ twice to get a simple graph $G_2$, and give the line graph $L(G_2)$ the edge weights $w_v(e,f)$ on pairs of edges meeting at an original vertex $v$ (weight $0$ on the subdivision pairs). Eulerian circuits of $G$ correspond bijectively, with equal cost, to Hamiltonian cycles of $L(G_2)$, so any TSP solver on $L(G_2)$ returns an optimal scaffold route; the construction is polynomial.
4. *(Tractable case.)* If $G$ is a $4$-regular plane graph and the crossing transition at every vertex is prohibited (the circuit follows faces), an optimal Eulerian circuit can be found in polynomial time.

## Expansion

In the hardness proof, $0/1$ turning costs restrict which transitions a zero-cost circuit may use at each literal and clause vertex of $G_I$, so that the zero-cost Eulerian circuits encode exactly the satisfying truth assignments. In the TSP reduction, the middle subdivision vertex $e_c$ of each original edge has degree $2$ in $L(G_2)$, so any Hamiltonian cycle passes $e_u,e_c,e_v$ consecutively and therefore traverses each original edge as a unit; consecutive original edges meet at a vertex and pay its turning cost. In the $4$-regular plane case, face $2$-colour $G$ and let $F$ be its Tait (black-face) graph, so that $G$ is the medial graph of $F$ and each vertex of $G$ is an edge of $F$. The two non-crossing transitions at a vertex are its black and white smoothings, and non-crossing Eulerian circuits (A-trails) of $G$ correspond bijectively to spanning trees of $F$ (an edge in the tree selects one smoothing at its vertex). Weighting each edge of $F$ by the cost difference between the two smoothings turns the problem into a minimum spanning tree computation. The results also apply to mill-routing and to biomolecular computation where an Eulerian strand route is designed.

## Depends on

- [Line graph of an edge-indexed multigraph](../../../../GraphTheory/paths-cycles-connectivity/eulerian-circuits/line-graph.md)

## Proof depends on

- [3SAT is NP-hard](../../../../TheoryOfComputation/np-completeness/satisfiability/3-satisfiability/sat3-dec-np-hard.md)
- [NP-hardness transfers along reductions](../../../../TheoryOfComputation/np-completeness/satisfiability/3-satisfiability/np-hard-of-poly-many-one-red.md)

## Sources

- Joanna A. Ellis-Monaghan, Andrew McDowell, Iain Moffatt, Greta Pangborn, "DNA origami and the complexity of Eulerian circuits with turning costs", arXiv:1309.4662 (2013), Definition 1 and Problems 1–3 (Section 2), Proposition 1, Theorem 1 and Corollaries 1–2 (Section 3), Theorem 2 (Section 4), Theorems 3–4 (Section 5), <https://doi.org/10.48550/arXiv.1309.4662>.
