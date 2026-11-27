# Reduction from monoid word consequences to mixed implication

Given a finite alphabet $\Gamma$, a finite set $E$ of equations between words in $\Gamma^*$ and a further equation $e$, one can effectively construct a finite database schema $S$, a finite set $F$ of FDs and INDs on $S$, and an IND $\sigma$ on $S$. The construction has both properties:

- $E$ implies $e$ under all homomorphisms into arbitrary monoids if and only if $F\models_{\rm unr}\sigma$.
- $E$ implies $e$ under all homomorphisms into finite monoids if and only if $F\models_{\rm fin}\sigma$.

Database values range over a fixed countably infinite set. The schema is not fixed: the construction uses attributes indexed by prefixes of words in the input. An IND conclusion already suffices for a reduction to the decision problems allowing either kind of conclusion.

## Depends on

- [Functional and inclusion dependencies on a schema](../dependency.md)
- [Finite implication of dependencies](../finitely-implies.md)
- [Unrestricted implication of dependencies](../implies.md)

## Expansion

The proof has three parts to establish separately. Encode a monoid countermodel using rows for pairs of word images and their products; only the image of the free monoid is needed, so its elements can be coded in the countable value domain. Conversely, extract a monoid on the generated word images from a database counterexample, using the FDs to make multiplication well defined. These translations preserve finite counterexamples: finitely many word images give finitely many rows, and a finite database has finite active domain. Finally replace the construction's auxiliary inclusion with a repeated left-hand attribute by proper distinct-position INDs on an extended schema, preserving both implications (Exercise 9.4(e)). The auxiliary inclusion itself is not an IND in the stated syntax.

## Proof depends on

- [Satisfaction of a schema dependency](../holds-in-2.md)
- [A joint witness for a projected row](../holds-in-iff-exists-row.md)
- [Finite extents and finite active domain](../is-finite-iff-finite-active-domain.md)

## Sources

- S. Abiteboul, R. Hull and V. Vianu, [*Foundations of Databases*](https://webdam.di.ens.fr/Alice/pdfs/all.pdf), Addison-Wesley, 1995, Theorem 9.2.4(a), construction and proof, pp. 199–202, and Exercise 9.4(e). The chapter's bibliographic notes credit the reduction to A. K. Chandra and M. Y. Vardi (1985).
