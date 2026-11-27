# Church–Rosser theorem for β-reduction

For all untyped λ-terms $M_1, M_2, M_3$: if $M_1 \twoheadrightarrow_\beta M_2$ and $M_1 \twoheadrightarrow_\beta M_3$, then there is a term $M_4$ with $M_2 \twoheadrightarrow_\beta M_4$ and $M_3 \twoheadrightarrow_\beta M_4$
(Church and Rosser, 1936).

The proof of Tait and Martin-Löf uses that $\twoheadrightarrow_\beta$ is the transitive closure of parallel reduction, which has the diamond property, and that the
diamond property passes from a relation $\Rightarrow$ to its transitive closure by two inductions: if $a \Rightarrow b$ and $a \Rightarrow^* c$, then $b \Rightarrow^* d$ and
$c \Rightarrow d$ for some $d$, by induction on the length of $a \Rightarrow^* c$; and then, by induction on the length of $a \Rightarrow^* b$, two paths from $a$ have a common
end.

## Depends on

- [β-reduction](beta-reduction.md)

## Proof depends on

- [Diamond property of parallel reduction](diamond-property-of-parallel-reduction.md)
- [Parallel β-reduction](parallel-beta-reduction.md)

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Definition 1.4.1, Lemma 1.4.2 and Theorem 1.4.7 (Church and Rosser).
- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 1, Theorem 1.24 (Church–Rosser).
- The CSLib formalization of the untyped λ-calculus with locally nameless terms proves the confluence of full β-reduction (`Cslib.LambdaCalculus.LocallyNameless.Untyped.Term.confluent_fullBeta`).
