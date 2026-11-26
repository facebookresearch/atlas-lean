# RNA structure prediction with arbitrary pseudoknots is NP-complete for input nearest-neighbour energies

In the Nearest Neighbour Pseudoknot Model of Lyngsø and Pedersen (2000, Definition 1), a secondary structure on a sequence $s \in \{A, C, G, U\}^n$ is a set $S$ of base pairs $i \cdot j$ with $1 \le i < j \le n$ in which each base is in at most one pair, with no restriction against crossing pairs, and its energy is

$$E(S) = \sum_{i \cdot j \in S} E(i \cdot j, i + 1, j - 1),$$

where the energy of a pair depends only on the types of the two paired bases, the types of the neighbouring bases $i + 1$ and $j - 1$, and, if a neighbour is itself paired, on its partner.

Proposition 1 of the source concerns the decision problem whose input is a sequence $s$, a base-pair energy function $E$ of this form (a finite table of values, part of the input), and a threshold value $E_0$, and which asks whether some secondary structure $S$ on $s$ has $E(S) < E_0$. The proposition states that this problem is NP-complete. Membership in NP is immediate, since $E(S)$ is computed in polynomial time, and hardness is proved by reduction from 3-SAT restricted so that each literal occurs at most twice: the reduction builds both the sequence and the energy function from the formula (the energy values depend on the number $d$ of binary digits used in the sequence encoding, and only Watson–Crick pairs can receive negative energy), so the sequence and the energy table are both input.

The result is a worst-case statement about this problem. It does not say that every fixed energy function makes pseudoknotted prediction hard: allowing crossing pairs alone does not cause hardness, and for the identically zero energy every structure is optimal, so the problem is trivial. In the source's words, a worst-case polynomial algorithm handling all energy functions of this model would imply P = NP, and an efficient algorithm for general pseudoknots must exploit properties of a specific energy function. The source contrasts this with secondary structure prediction without pseudoknots, which it describes as solvable in polynomial time.

## Expansion

1. The model: secondary structures with crossing pairs, the nearest-neighbour energy, and the decision problem with sequence, energy table and threshold as input.
2. Membership in NP.
3. The reduction from the restricted 3-SAT: variable and clause blocks of the sequence whose helices and stacking energies encode satisfying assignments.
4. The remarks of the source on G–U pairs and on stacking energies, and the consequence for richer energy models that specialize to this one.

## Sources

- R. B. Lyngsø and C. N. S. Pedersen, Pseudoknots in RNA secondary structures, BRICS Report Series RS-00-1, University of Aarhus, 2000, Definition 1, Proposition 1 and Section 5.
