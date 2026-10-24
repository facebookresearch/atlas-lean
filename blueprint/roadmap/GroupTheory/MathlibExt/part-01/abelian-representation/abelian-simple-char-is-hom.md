---
article_id: af_1e49b8d72f9c489802a59007
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.AbelianRepresentationWanted.abelian_simple_char_is_hom
---

# Abelian simple char is hom

The character of a simple complex representation of a finite abelian group is
a monoid homomorphism.

Proof: Categorical simplicity gives irreducibility, then Mathlib's commutative irreducible
representation theorem makes `V` one-dimensional (the corollary in Wikipedia, “Schur's lemma”,
that complex irreducible representations of abelian groups are one-dimensional). Rank-one
endomorphisms are scalars, and their traces give the multiplicative character.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Character Monoid Hom](character-monoid-hom.md)
- [Coe character Monoid Hom](coe-character-monoid-hom.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.AbelianRepresentation](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "representations of abelian groups"; J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2.8 (degree-one characters of abelian groups).
