# Clausal normal form preserves satisfiability

Let $F$ be a closed first-order formula. Transform it into prenex form and Skolemize it as in [Skolemization preserves satisfiability](skolemization-preserves-satisfiability.md), obtaining $\forall x_1 \dots x_m\, H$ with $H$ quantifier-free, and then transform $H$ into an equivalent conjunctive normal form, obtaining $F' = \forall x_1 \dots x_m \bigwedge_{i=1}^k \bigvee_{j=1}^{n_i} L_{ij}$ with literals $L_{ij}$. The set $N = \{C_1, \dots, C_k\}$ of clauses $C_i = \bigvee_j L_{ij}$, with their variables read as universally quantified, is the *clausal normal form* of $F$. Then $F' \models F$, the converse failing in general, and

$$F \text{ is satisfiable} \iff F' \text{ is satisfiable} \iff N \text{ is satisfiable}.$$

## Depends on

- [Skolemization preserves satisfiability](skolemization-preserves-satisfiability.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 3.5, the complete picture of the normal form transformations and Theorems 3.10 and 3.11, p. 57.
