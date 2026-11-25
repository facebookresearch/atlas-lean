# Lifting lemma for first-order resolution

Read clauses as finite multisets of literals. Let $C_1$ and $C_2$ be first-order clauses with no variables in common and $\theta_1$, $\theta_2$ substitutions such that $C_1\theta_1$ and $C_2\theta_2$ are ground. If $D$ is obtained from $C_1\theta_1$ and $C_2\theta_2$ by a ground resolution step, which removes one occurrence of a literal $L$ from one clause and of its complement from the other, then there are a resolvent $C$ of $C_1$ and $C_2$, computed with a most general unifier of the two literals resolved upon, and a substitution $\rho$ with $D = C\rho$. Likewise, a ground factoring step on $C_1\theta_1$ lifts to a factoring step on $C_1$ with a most general unifier.

## Proof depends on

- [Unification returns a most general unifier](../first-order-unification/is-mgu-unify.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- N-ary ranked-signature adapter for curried unification (proof prerequisite)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, 2019/20, Section 3.11, the general resolution and factorization rules and Lemma 3.30, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>
- J. A. Robinson, "A machine-oriented logic based on the resolution principle", *Journal of the ACM* 12(1):23–41, 1965
- M. Fitting, *First-Order Logic and Automated Theorem Proving*, 2nd ed., Springer, 1996
