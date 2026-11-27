# Soundness of first-order binary resolution and factoring

Let $C_1 \vee L_1$ and $C_2 \vee \neg L_2$ be first-order clauses with no variables in common, and $\sigma$ a most general unifier of the atoms $L_1$ and $L_2$. Their binary resolvent $\sigma(C_1 \vee C_2)$ is a logical consequence of the two clauses (read as universally closed). If $\sigma$ is a most general unifier of two literals $L, L'$ of a clause $C \vee L \vee L'$, its factor $\sigma(C \vee L)$ is a logical consequence of it. Consequently, if the empty clause is derivable from a set $S$ of clauses by binary resolution, factoring and renaming of variables, then $S$ is unsatisfiable.

## Depends on

- [Most general unifier](../first-order-unification/is-mgu.md)
- [Unification of ranked terms through the curried encoding](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)

## Proof depends on

- [Unification returns a most general unifier](../first-order-unification/is-mgu-unify.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, 2019/20, Section 3.11, the general resolution calculus and Proposition 3.32, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>
- J. A. Robinson, "A machine-oriented logic based on the resolution principle", *Journal of the ACM* 12(1):23–41, 1965
- M. Fitting, *First-Order Logic and Automated Theorem Proving*, 2nd ed., Springer, 1996
