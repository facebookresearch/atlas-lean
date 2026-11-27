# Type reconstruction for simple types is P-complete

For [simple type assignment à la Curry](simple-type-assignment-a-la-curry.md):

1. **Reduction to unification.** From a pure term $M$ one computes in logarithmic space a system $E_M$ of first-order equations between types and a
   type $\tau_M$, using a fresh type variable $\alpha_x$ for each variable $x$ of $M$ (after renaming bound variables apart from each other and from the free ones, so that each variable is bound at most once), such that $M$ is typable exactly when $E_M$ has a solution. With
   $\Gamma_M = \{x : \alpha_x \mid x \in \mathrm{FV}(M)\}$, each solution $S$ yields the typing $S(\Gamma_M) \vdash M : S(\tau_M)$, and every typing $\Gamma \vdash M : \rho$ arises from a
   solution $S$ with $S(\alpha_x) = \Gamma(x)$ for $x \in \mathrm{FV}(M)$ and $\rho = S(\tau_M)$.
2. **Principal types.** Every typable term has a principal pair, obtained from a most general solution of $E_M$.
3. **Complexity.** First-order unification is P-complete under logarithmic-space reductions (Dwork, Kanellakis and Mitchell). Conversely, unification
   over any signature reduces in logarithmic space to unification over the single binary symbol $\to$ with one equation, and an equation $\tau = \sigma$ to the
   typability of a term built from $\tau$ and $\sigma$; hence type reconstruction for simple types is P-complete.

## Depends on

- [Simple type assignment à la Curry](simple-type-assignment-a-la-curry.md)
- [Log-space many-one reductions](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/log-space-red.md)
- [Lists of equations](../../../../Logic/first-order-logic/first-order-unification/equations.md)
- [Unifier of a list of equations](../../../../Logic/first-order-logic/first-order-unification/unifies.md)
- [Polynomial time on multi-tape machines](../../../../TheoryOfComputation/complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)

## Proof depends on

- [Unification returns a most general unifier](../../../../Logic/first-order-logic/first-order-unification/is-mgu-unify.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 6.3.6 (unification is P-complete), Proposition 6.3.8 (principal solutions), Theorem 6.4.1 (type reconstruction is P-complete), Definition 6.4.2 and Lemma 6.4.3 (the equations $E_M$ and their solutions), Corollary 6.4.5 (principal pairs), the reduction after Example 6.4.6, and Exercises 6.8.5 and 6.8.7 (one equation, arrow-only signature).
