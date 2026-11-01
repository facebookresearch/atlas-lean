---
article_id: af_e1230a58e9122a94672ff8c8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.GroupTheory.ClassFunctionWanted.isClassFunction_iff_factor_conjClasses
---

# Is Class Function iff factor conj Classes

A function is a class function iff it factors through the quotient onto
conjugacy classes.

Proof: Descend a class function with `Quotient.lift`, using `isConj_iff` for
well-definedness, and use equality in `ConjClasses` for the converse.

## Depends on

- [Is Class Function](is-class-function.md)

## Proof depends on

- [Eq of is Conj](eq-of-is-conj.md)

## Sources

- [MathlibExt, MathlibExt.GroupTheory.ClassFunction](../../../../../sources/v2/MathlibExt.md)
- `undergrad.yaml`, section "Representation theory of finite groups", entry "class function over a group"; J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2 (class functions as functions on conjugacy classes).
