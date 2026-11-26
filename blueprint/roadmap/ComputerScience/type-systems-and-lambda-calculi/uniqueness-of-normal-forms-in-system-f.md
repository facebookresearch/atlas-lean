# Uniqueness of normal forms in System F

Every well-typed term of System F has exactly one normal form under [one-step full reduction](system-f/scoped-pure-system-f/full-step.md): by [strong normalization](normalization-and-logical-relations/strong-normalization-of-system-f.md) every maximal reduction sequence from it is finite and so ends in a normal form, hence a normal form exists, and by confluence any two normal forms of the term coincide.

## Depends on

- [One-step full reduction of System F terms](system-f/scoped-pure-system-f/full-step.md)

## Proof depends on

- [Strong normalization of System F](normalization-and-logical-relations/strong-normalization-of-system-f.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Confluence (the Church–Rosser property) of full reduction of System F terms (proof prerequisite)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapters 11 and 14, <https://www.paultaylor.eu/stable/prot.pdf>
