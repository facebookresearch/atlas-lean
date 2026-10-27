---
article_id: af_891a01868419a8e299865951
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.IrreducibleCharacterBasisWanted.mem_span_irrCharacters_of_isClassFunction
---

# Mem span irr Characters of is Class Function

Every class function is a linear combination of irreducible characters.

Proof: Subtract the orthogonal projection onto the irreducible characters. The
remainder vanishes by Schur's lemma, Maschke's theorem, and the regular
representation on a small model of the complex group algebra, as in the proof of
Teleman's Theorem 9.3 (completeness of characters).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Eq zero of is Class Function of orthogonal](eq-zero-of-is-class-function-of-orthogon.md)
- [Character is Class Function](../../part-01/class-function/character-is-class-function.md)
- [Linear Independent irr Characters](linear-independent-irr-characters.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.IrreducibleCharacterBasis](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "orthonormal basis of irreducible characters"; J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2.7, Theorem 6 (irreducible characters span the class functions).
