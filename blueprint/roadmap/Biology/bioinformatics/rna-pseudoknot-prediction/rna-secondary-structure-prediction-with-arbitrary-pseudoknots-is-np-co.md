# RNA secondary structure prediction with arbitrary pseudoknots is NP-complete

In the Nearest Neighbour Pseudoknot Model of Lyngsø and Pedersen (2000, Definition 1), a secondary structure on a sequence $s \in \{A, C, G, U\}^n$ is a set $S$ of base pairs $i \cdot j$ with $1 \le i < j \le n$ in which each base is in at most one pair, with no restriction against crossing pairs, and its energy is
$$E(S) = \sum_{i \cdot j \in S} E(i \cdot j, i + 1, j - 1),$$
where the energy of a pair depends only on the types of the two paired bases, the types of the neighbouring bases $i + 1$ and $j - 1$, and, if a neighbour is itself paired, on its partner. Proposition 1 of the source states that deciding whether the optimal secondary structure in this model has energy lower than a given value is NP-complete. Membership in NP is immediate, and hardness is proved by reduction from 3-SAT restricted so that each literal occurs at most twice. The source contrasts this with secondary structure prediction without pseudoknots, which it describes as solvable in polynomial time.

## Expansion

1. The model: secondary structures with crossing pairs, the nearest-neighbour energy, and the decision problem.
2. Membership in NP.
3. The reduction from the restricted 3-SAT: variable and clause blocks of the sequence whose helices and stacking energies encode satisfying assignments.
4. The remarks of the source on G–U pairs and on stacking energies, and the consequence for richer energy models that specialize to this one.

## Sources

- R. B. Lyngsø and C. N. S. Pedersen, Pseudoknots in RNA secondary structures, BRICS Report Series RS-00-1, University of Aarhus, 2000, Definition 1 and Proposition 1.
