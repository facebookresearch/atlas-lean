# Type reconstruction for simple types is P-complete

For [simple type assignment à la Curry](simple-type-assignment-a-la-curry.md):

1. **Reduction to unification.** From a pure term $M$ one computes in logarithmic space a system $E_M$ of first-order equations between types and a
   type $\tau_M$ such that $M$ is typable exactly when $E_M$ has a solution, and each solution $S$ yields the typing $S(\Gamma_M) \vdash M : S(\tau_M)$.
2. **Principal types.** Every typable term has a principal pair, obtained from a most general solution of $E_M$.
3. **Complexity.** First-order unification over the single binary symbol $\to$ is P-complete under logarithmic-space reductions (Dwork, Kanellakis and
   Mitchell), and it reduces back to type reconstruction; hence type reconstruction for simple types is P-complete.

## Depends on

- [Simple type assignment à la Curry](simple-type-assignment-a-la-curry.md)

## Proof depends on

- [Unification returns a most general unifier](../../../Logic/first-order-logic/first-order-unification/is-mgu-unify.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 6.3.6 (unification is P-complete), Proposition 6.3.8 (principal solutions), Theorem 6.4.1 (type reconstruction is P-complete), Lemma 6.4.3 and Corollary 6.4.5 (principal pairs).
