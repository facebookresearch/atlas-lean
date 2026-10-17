---
article_id: af_e485a842925179e7cea33d1c
declaration: def
origin: cited
statement: formalized
lean: NumberField.primitiveIntMinpoly
---

# Absolute

A primitive integral normalization of the rational minimal polynomial of `x`.

For algebraic `x`, this is a primitive integral representative of `minpoly ℚ x`. For
nonalgebraic `x`, Mathlib defines `minpoly ℚ x` to be zero, and `primPart` consequently gives its
conventional fallback value `1`. The sign is immaterial for applications to Mahler measure.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Height.Absolute](../../../../../sources/v2/MathlibExt.md)
