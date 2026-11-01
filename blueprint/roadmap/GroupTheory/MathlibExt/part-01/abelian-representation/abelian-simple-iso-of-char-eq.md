---
article_id: af_a5d2e62c4989ce114bf542e0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.AbelianRepresentationWanted.abelian_simple_iso_of_char_eq
---

# Abelian simple iso of char eq

Simple complex representations of a finite abelian group with equal characters
are isomorphic.

Proof: Mathlib's character orthonormality formula gives inner product one for `V` with itself.
Replacing the second character by the equal character of `W` forces `V ≅ W`. This is the
orthonormality of irreducible characters in Wikipedia, “Character theory”.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GroupTheory.AbelianRepresentation](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "representations of abelian groups"; J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2.8 (characters determine representations of abelian groups).
