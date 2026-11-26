# The standardization theorem

Call a redex of a term *internal* if it is not the head redex. An *internal reduction* contracts an internal redex at each step, a *head reduction* the
head redex, and a *standard reduction* is a head reduction followed by an internal one.

**Theorem.** If $t \twoheadrightarrow_\beta t'$, then there is a standard reduction from $t$ to $t'$. Moreover there is one that is *strongly standard*: the redexes contracted
have non-decreasing rank, the rank counting redexes from left to right by the position of their λ.

Consequently a term is β-convertible to a head normal form if and only if its head reduction terminates, and if $t =_\beta \lambda x.\, u$ then some term reached from
$t$ by head reduction has the form $\lambda x.\, v$.

## Depends on

- [β-reduction](beta-reduction.md)
- [Head normal forms and solvable terms](../solvability-and-bohm-s-theorem/head-normal-forms-and-solvable-terms.md)

## Proof depends on

- [The finite developments theorem](../solvability-and-bohm-s-theorem/finite-developments-theorem.md)
- [Church–Rosser theorem for β-reduction](church-rosser-theorem-for-beta-reduction.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 4, Section 3: the definitions of internal, head and standard reductions, Theorem 4.39 (standardization), Corollaries 4.43–4.44, the definition of rank and Theorem 4.45 (standardization, second form).
