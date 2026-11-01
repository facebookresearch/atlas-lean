---
article_id: af_26722584ad0f3207396576c6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.AbelianRepresentationWanted.abelian_hom_is_simple_char
---

# Abelian hom is simple char

Every monoid homomorphism to `ℂ` is the character of a simple complex
representation of a finite abelian group.

Proof: Let `g` act on the one-dimensional space `ℂ` by the scalar `φ g`; its trace is `φ g`.
One-dimensional modules are simple. Wikipedia, “Representation theory of finite groups”, notes that
the irreducible characters of an abelian group are its homomorphisms to `ℂˣ`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Of Monoid Hom](of-monoid-hom.md)
- [Of Monoid Hom character](of-monoid-hom-character.md)
- [Of Monoid Hom simple](of-monoid-hom-simple.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.AbelianRepresentation](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "representations of abelian groups"; J.-P. Serre, Linear Representations of Finite Groups, GTM 42, Ch. I (one-dimensional representations from characters).
