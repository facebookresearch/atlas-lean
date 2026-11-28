# Satisfiability of ReLU GNNs is undecidable even without global readout

With the unbounded ReLU activation, satisfiability and universal satisfiability of graph neural networks are undecidable already for local GNNs (no global readout) that aggregate over in- and out-neighbors, and for outgoing-only GNNs with global readout. Local outgoing-only ReLU GNNs have NEXPTIME-complete satisfiability.

**Theorem (Benedikt, Lu and Tan).** For aggregate-combine GNNs with rational coefficients and ReLU activations $x \mapsto \max(x, 0)$, the following problems are undecidable, with the GNN as input:

1. satisfiability (some finite graph has a vertex the GNN accepts) for local GNNs, which aggregate over out- and in-neighbors but have no global readout;
2. satisfiability for outgoing-only GNNs with global readout;
3. universal satisfiability (some finite graph has all its vertices accepted) for each of these two classes.

The local results also hold over undirected graphs. In contrast, satisfiability of local outgoing-only ReLU GNNs is NEXPTIME-complete, and for local GNNs with truncated ReLU activations satisfiability is PSPACE-complete.

## Depends on

- [Aggregate-combine graph neural networks](aggregate-combine-graph-neural-networks.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Satisfiability is reduced from the solvability over $\mathbb{N}$ of simple equation systems ($v_{t_1} = 1$, $v_{t_1} = v_{t_2} + v_{t_3}$, $v_{t_1} = v_{t_2} \cdot v_{t_3}$). Values of variables are encoded by numbers of colored vertices, which sums over neighbors or over the whole graph can read off; unbounded ReLU lets the network compute and compare such counts exactly, including the checks for products, so the constructed GNN is satisfiable exactly when the system is solvable. For outgoing-only GNNs with global readout the same network accepts either every vertex or none, giving universal satisfiability; for local bidirectional GNNs universal satisfiability is reduced from the halting problem of two-counter machines.

## Sources

- Michael Benedikt, Chia-Hsuan Lu, Boris Motik and Tony Tan, "Decidability of Graph Neural Networks via Logical Characterizations", 51st International Colloquium on Automata, Languages, and Programming (ICALP 2024), LIPIcs 297, Article 127, 2024, <https://doi.org/10.4230/LIPIcs.ICALP.2024.127>; Michael Benedikt, Chia-Hsuan Lu and Tony Tan, same title, ACM Transactions on Computational Logic 27(2):1–65, 2026, <https://doi.org/10.1145/3800944>; read in arXiv:2404.18151v4, <https://arxiv.org/abs/2404.18151v4>: Theorems 6.9 and 6.10 (satisfiability) in Section 6.2, Theorems 6.15 and 6.18 (universal satisfiability) in Section 6.3, their undirected versions in Appendix A, and the summary tables of Section 3.1, in the numbering of that version.
