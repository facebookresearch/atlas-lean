# Satisfiability of truncated-ReLU GNNs with global readout is undecidable

No algorithm decides whether a graph neural network with truncated ReLU activations and global readout accepts some vertex of some graph, nor whether it accepts every vertex of some graph. Without global readout the same problems are decidable.

**Theorem (Benedikt, Lu and Tan).** For aggregate-combine GNNs with rational coefficients, truncated ReLU activations $x \mapsto \min(\max(x, 0), 1)$, aggregation over both out- and in-neighbors, and global readout (the class $\mathrm{trReLU}$-GNN with no locality or direction restriction), the following problems are undecidable, with the GNN as input:

1. satisfiability: is there a finite graph and a vertex that the GNN accepts?
2. universal satisfiability: is there a finite graph all of whose vertices the GNN accepts?

Both remain undecidable over undirected graphs. The underlying logical result is that finite satisfiability of the two-variable modal logic with Presburger quantifiers and global counting, $\mathrm{MP}^2$, is undecidable. In contrast, satisfiability is decidable for local (no global readout) GNNs with eventually constant activations such as truncated ReLU, and PSPACE-complete for local truncated-ReLU GNNs.

## Depends on

- [Aggregate-combine graph neural networks](aggregate-combine-graph-neural-networks.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The reduction is from Hilbert's tenth problem in the form of *simple equation systems*, whose equations are $v_{t_1} = 1$, $v_{t_1} = v_{t_2} + v_{t_3}$ or $v_{t_1} = v_{t_2} \cdot v_{t_3}$ with pairwise distinct indices; solvability over $\mathbb{N}$ is undecidable. For each system an $\mathrm{MP}^2$ formula describes graphs in which the value of $v_t$ is the size of a set of vertices of color $U_t$, global counting enforces the equations, and products are encoded by requiring exactly one edge from each vertex of one set into another. The formula is finitely satisfiable exactly when the system is solvable, and every $\mathrm{MP}^2$ formula is equivalent to a truncated-ReLU GNN with global readout, which transfers undecidability to satisfiability; the same reduction gives graphs in which every vertex is accepted, giving universal satisfiability.

## Sources

- Michael Benedikt, Chia-Hsuan Lu, Boris Motik and Tony Tan, "Decidability of Graph Neural Networks via Logical Characterizations", 51st International Colloquium on Automata, Languages, and Programming (ICALP 2024), LIPIcs 297, Article 127, 2024, <https://doi.org/10.4230/LIPIcs.ICALP.2024.127>; Michael Benedikt, Chia-Hsuan Lu and Tony Tan, same title, ACM Transactions on Computational Logic 27(2):1–65, 2026, <https://doi.org/10.1145/3800944>; read in arXiv:2404.18151v4, <https://arxiv.org/abs/2404.18151v4>: Theorems 4.16 (finite satisfiability of $\mathrm{MP}^2$), 4.19 and 4.20 (satisfiability and universal satisfiability of truncated-ReLU GNNs with global readout) in Section 4.2, their undirected versions in Appendix A, and the summary tables of Section 3.1, in the numbering of that version.
