# Panteleev-Kalachev: asymptotically good quantum LDPC codes exist

There are explicit families of quantum LDPC codes $[[n, k, d]]$ with $k = \Theta(n)$ and $d = \Theta(n)$ (and constant check weight), obtained as lifted products $\mathrm{LP}(A, B^{*})$ over the group algebra of a non-abelian group $G$ whose Cayley graphs are expanders, with matrices $A$, $B$ encoding random local codes. The same construction yields asymptotically good classical LDPC codes that are locally testable with constant query complexity and constant soundness ($c^3$-LTCs), proving the qLDPC conjecture and, independently of Dinur et al., the $c^3$-LTC conjecture.

## Proof sketch

The lifted product of two matrices over $\mathbb{F}_2[G]$ corresponds to a square complex on $G$ with local codes, essentially a left-right Cayley complex. Distance is proved via product-expansion of the local codes combined with spectral expansion of the Cayley graphs, as in the quantum Tanner analysis; local testability of the classical code follows from the same expansion of the corresponding chain complex (a coboundary expansion statement) one dimension higher.

## Depends on

- [Lifted product codes over group algebras](../homological-quantum-ldpc-codes/lifted-product-codes-over-group-algebras.md)
- [Quantum LDPC code families and asymptotically good quantum codes](../homological-quantum-ldpc-codes/quantum-ldpc-code-families-and-good-codes.md)
- [Locally testable code](../../../InformationTheory/error-correcting-codes/locally-testable-codes/ltc.md)

## Proof depends on

- [Random pairs of codes and their duals are product-expanding](random-pairs-of-codes-are-product-expanding.md)
- [Good locally testable codes of every rate below one](../../../InformationTheory/error-correcting-codes/locally-testable-codes/theorem-1-2.md)

## Sources

- Pavel Panteleev, Gleb Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022); arXiv:2111.03654.
