# Lifting lemma for first-order resolution

Read clauses as finite multisets of literals. Let $C_1$ and $C_2$ be first-order clauses with no variables in common and $\theta_1$, $\theta_2$ substitutions such that $C_1\theta_1$ and $C_2\theta_2$ are ground. If $D$ is obtained from $C_1\theta_1$ and $C_2\theta_2$ by a ground resolution step, which removes one occurrence of a literal $L$ from one clause and of its complement from the other, then there are a resolvent $C$ of $C_1$ and $C_2$, computed with a most general unifier of the atoms $B$ and $A$ of the two literals $B$ and $\neg A$ resolved upon (two literals of opposite sign are never unifiable themselves), and a substitution $\rho$ with $D = C\rho$. Likewise, a ground factoring step on $C_1\theta_1$, which merges two literals of the same sign, lifts to a factoring step on $C_1$ with a most general unifier of their atoms.

## Depends on

- [Most general unifier](../first-order-unification/is-mgu.md)
- [Unification of ranked terms through the curried encoding](../first-order-unification/unification-of-ranked-terms-through-the-curried-encoding.md)

## Proof depends on

- [Unification returns a most general unifier](../first-order-unification/is-mgu-unify.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, 2019/20, Section 3.11, the general resolution and factorization rules and Lemma 3.30, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>
- J. A. Robinson, "A machine-oriented logic based on the resolution principle", *Journal of the ACM* 12(1):23–41, 1965
- M. Fitting, *First-Order Logic and Automated Theorem Proving*, 2nd ed., Springer, 1996
