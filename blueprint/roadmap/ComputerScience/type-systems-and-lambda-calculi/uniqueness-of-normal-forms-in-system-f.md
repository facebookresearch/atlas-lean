# Uniqueness of normal forms in System F

Every well-typed term of System F has exactly one normal form under [one-step full reduction](system-f/scoped-pure-system-f/full-step.md): by [strong normalization](strong-normalization-of-system-f.md) every reduction sequence from it reaches a normal form, and by confluence any two of these coincide.

## Depends on

- [One-step full reduction of System F terms](system-f/scoped-pure-system-f/full-step.md)

## Proof depends on

- [Strong normalization of System F](strong-normalization-of-system-f.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Confluence (the Church–Rosser property) of full reduction of System F terms (proof prerequisite)

## Sources

- J.-Y. Girard, Y. Lafont and P. Taylor, *Proofs and Types*, Cambridge University Press, 1989, Chapters 11 and 14, <https://www.paultaylor.eu/stable/prot.pdf>
