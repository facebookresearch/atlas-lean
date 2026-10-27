---
article_id: af_2f189b5952fabbe4e9091fb8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant.hadamard_determinant_inequality
---

# Hadamard Determinant

Hadamard's determinant inequality for a complex `n × n` matrix:
`‖det A‖ ≤ ∏ i, √(∑ j, ‖A i j‖^2)` via `normSq`,
i.e. `‖det A‖ ≤ ∏ i, sqrt(∑ j, normSq(A i j))`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant](../../../../../sources/v2/MathlibExt.md)
- J. Hadamard, Résolution d'une question relative aux déterminants, Bulletin des Sciences Mathématiques 17 (1893), 240–246.
