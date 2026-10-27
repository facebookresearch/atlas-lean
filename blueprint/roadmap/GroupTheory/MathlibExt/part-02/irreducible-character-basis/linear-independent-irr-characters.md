---
article_id: af_32400a0bf47907a6539bd4fd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted.linearIndependent_irrCharacters
---

# Linear Independent irr Characters

Distinct irreducible complex characters are linearly independent as functions.

Proof: Apply row orthogonality (C. Teleman, *Representation Theory*, Cambridge lecture
notes, 2005, Theorem 8.10) as coordinate functionals to a vanishing finite linear
combination of pairwise distinct irreducible characters.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Linear Independent character](linear-independent-character.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.IrreducibleCharacterBasis](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "orthonormal basis of irreducible characters"; J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2.5 (independence of irreducible characters).
