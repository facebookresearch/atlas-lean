---
article_id: af_307967d150d835bcb67e07b4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted.isReducedRowEchelon_unique_of_rowEquivalent
---

# Is Reduced Row Echelon unique of row Equivalent

The reduced row echelon form in a row-equivalence class is unique.

Proof: Reindex the columns along the order isomorphism with `Fin (Fintype.card n)`. For `Fin`
columns, induct on the number of columns: the matrices agree on all but the last column by
induction, and that forces their last columns to agree.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Col eq single of is Leading Entry](col-eq-single-of-is-leading-entry.md)
- [Submatrix order Iso](submatrix-order-iso.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelon](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Matrices / row-reduced matrices; G. Strang, Introduction to Linear Algebra, 6th ed., Wellesley-Cambridge Press (2023), Section 2.2.
