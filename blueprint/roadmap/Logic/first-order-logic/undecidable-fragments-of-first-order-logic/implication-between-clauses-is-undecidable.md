# Implication between clauses is undecidable

There is no algorithm that decides, for two first-order clauses $C$ and $D$, whether every model of $C$ is a model of $D$, although the stronger relation of θ-subsumption between clauses is decidable.

**Clauses.** A clause is a finite set of literals, atomic formulas or negated atomic formulas of first-order logic with function symbols, read as the universal closure of their disjunction. A clause $C$ *implies* a clause $D$, written $C \Rightarrow D$, if every model of $C$ is a model of $D$. $C$ *θ-subsumes* $D$ if $C\theta \subseteq D$ for some substitution $\theta$.

**Theorem (Schmidt-Schauß).** There is no procedure that decides, given clauses $C$ and $D$, whether $C \Rightarrow D$.

θ-subsumption implies implication, and θ-subsumption between clauses is decidable (Robinson). Implication between Horn clauses is undecidable as well (Marcinkowski and Pacholski).

## Depends on

None.

## Proof depends on

None.

## Expansion

Implication and θ-subsumption differ even for function-free clauses: $p(x,y,z) \vee \neg p(y,z,x)$ and $p(x,y,z) \vee \neg p(z,x,y)$ are equivalent under implication, each being a resolvent of the other with itself, while neither θ-subsumes the other. The copy read states the theorem without proof, citing Schmidt-Schauß; the original reduction is not reproduced here. The undecidability of implication is why generalization under implication in inductive logic programming is studied through decidable restrictions.

## Sources

- M. Schmidt-Schauß, "Implication of clauses is undecidable", *Theoretical Computer Science* 59(3):287–296, 1988, doi:10.1016/0304-3975(88)90146-6 (original source, cited beside the copy read).
- P. Idestam-Almquist, "Generalization of clauses under implication", *Journal of Artificial Intelligence Research* 3:467–489, 1995, doi:10.1613/jair.194; read as arXiv:cs/9512103v1, <https://arxiv.org/abs/cs/9512103v1>: Section 2 (clauses, θ-subsumption, Theorem 1, the definition of implication, Proposition 3) and Theorem 4 (undecidability of implication between clauses).
