# Consequences of the Church–Rosser theorem

For untyped λ-terms:

1. $M =_\beta N$ if and only if $M \twoheadrightarrow_\beta L$ and $N \twoheadrightarrow_\beta L$ for some term $L$;
2. a term has at most one β-normal form: if $M \twoheadrightarrow_\beta N_1$ and $M \twoheadrightarrow_\beta N_2$ with $N_1$, $N_2$ β-normal, then $N_1 = N_2$;
3. distinct β-normal forms are not β-convertible, and a term that is not β-normalizable is not β-convertible to a β-normal form;
4. hence β-conversion does not identify all terms: for example $\lambda x.\, x \ne_\beta \lambda x\, y.\, x$.

## Depends on

- [β-reduction](beta-reduction.md)

## Proof depends on

- [Church–Rosser theorem for β-reduction](church-rosser-theorem-for-beta-reduction.md)
- [The Church–Rosser property is equivalent to confluence](../../../../Logic/first-order-logic/term-rewriting/church-rosser-property-and-confluence.md): for part 1

## Sources

- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Corollaries 1.4.8–1.4.10, Example 1.4.11 and Remark 1.4.12.
- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 1, Proposition 1.27 and the remark after it.
