# Diamond property of parallel reduction

[Parallel β-reduction](parallel-beta-reduction.md) has the diamond property: if $M_1 \Rightarrow M_2$ and $M_1 \Rightarrow M_3$, then there is a term $M_4$ with $M_2 \Rightarrow M_4$ and
$M_3 \Rightarrow M_4$.

The proof is by induction on the derivation of $M_1 \Rightarrow M_2$, with a case analysis of $M_1 \Rightarrow M_3$; the case of two contractions of the same redex uses that
parallel reduction is substitutive.

## Depends on

- [Parallel β-reduction](parallel-beta-reduction.md)

## Proof depends on

- [Parallel reduction is substitutive](parallel-reduction-is-substitutive.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Lemma 1.4.5.
- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 1, Lemma 1.25 and the proof of Theorem 1.24.
- The CSLib formalization of the untyped λ-calculus with locally nameless terms proves the diamond property of parallel reduction (`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.parallel_diamond`).
