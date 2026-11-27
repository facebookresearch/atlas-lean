# Parallel reduction is substitutive

If $M \Rightarrow M'$ and $N \Rightarrow N'$ in [parallel β-reduction](parallel-beta-reduction.md), then $M[x := N] \Rightarrow M'[x := N']$.

The proof is by induction on the derivation of $M \Rightarrow M'$; in the case $M' = M$ it proceeds by induction on $M$.

## Depends on

- [Parallel β-reduction](parallel-beta-reduction.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Lemma 1.4.4.
- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 1, Lemma 1.26.
- The CSLib formalization of the untyped λ-calculus with locally nameless terms proves the substitutivity of parallel reduction (`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.para_subst`).
