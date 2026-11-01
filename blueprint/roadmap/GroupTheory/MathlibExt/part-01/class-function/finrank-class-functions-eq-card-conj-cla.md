---
article_id: af_18c4d4de6579d215bcde77b7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.ClassFunctionWanted.finrank_classFunctions_eq_card_conjClasses
---

# Finrank class Functions eq card conj Classes

The space of class functions has dimension equal to the number of conjugacy
classes.

Proof: Use `classFunctionsEquivConjClasses` and
`Module.finrank_fintype_fun_eq_card`, after obtaining a finite quotient from
`ConjClasses.mk_surjective`.

## Depends on

- [Class Functions](class-functions.md)

## Proof depends on

- [Class Functions Equiv Conj Classes](class-functions-equiv-conj-classes.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.ClassFunction](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "class function over a group"; J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2.7, Theorem 6 (dimension count for class functions).
