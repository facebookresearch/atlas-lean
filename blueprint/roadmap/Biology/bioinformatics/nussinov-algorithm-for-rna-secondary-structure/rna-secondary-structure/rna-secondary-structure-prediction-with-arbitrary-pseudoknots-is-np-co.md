# RNA structure prediction with arbitrary pseudoknots is NP-complete for input nearest-neighbour energies

In the nearest neighbour pseudoknot model of Lyngsø and Pedersen (2000), a secondary structure on a sequence $s \in \{A, C, G, U\}^n$ is a set $S$ of base pairs $i \cdot j$ with $1 \le i < j \le n$ in which each base is in at most one pair, with no restriction against crossing pairs, and its energy is

$$E(S) = \sum_{i \cdot j \in S} E(i \cdot j, i + 1, j - 1),$$

where the energy of a pair depends only on the types of the two paired bases, the types of the neighbouring bases $i + 1$ and $j - 1$, and, if a neighbour is itself paired, on its partner.

The decision problem has as input a sequence $s$, a base-pair energy function $E$ of this form (a finite table of values, part of the input), and a threshold value $E_0$, and asks whether some secondary structure $S$ on $s$ has $E(S) < E_0$. Lyngsø and Pedersen prove that this problem is NP-complete. Membership in NP is immediate, since $E(S)$ is computed in polynomial time, and hardness is proved by a reduction from 3-SAT that builds both the sequence and the energy function from the formula, so the sequence and the energy table are both input.

The result is a worst-case statement about this problem. It does not say that every fixed energy function makes pseudoknotted prediction hard: allowing crossing pairs alone does not cause hardness, and for the identically zero energy every structure is optimal, so the problem is trivial. What follows from NP-completeness is that a worst-case polynomial algorithm handling all energy functions of this model would imply P = NP. By contrast, secondary structure prediction without pseudoknots is solvable in polynomial time, as the paper recalls.

## Expansion

1. The model: secondary structures with crossing pairs, the nearest-neighbour energy, and the decision problem with sequence, energy table and threshold as input.
2. Membership in NP.
3. The reduction from 3-SAT: blocks of the sequence for variables and clauses, whose helices and pair energies encode satisfying assignments.
4. The extension of hardness to the larger class of energy models that specialize to this one.

## Sources

- R. B. Lyngsø and C. N. S. Pedersen, RNA pseudoknot prediction in energy-based models, J. Comput. Biol. 7 (2000), 409–427. <https://doi.org/10.1089/106652700750050862>
- R. B. Lyngsø and C. N. S. Pedersen, Pseudoknots in RNA secondary structures, in Proceedings of the Fourth Annual International Conference on Computational Molecular Biology (RECOMB 2000), ACM, 2000, 201–209. <https://doi.org/10.1145/332306.332551>
