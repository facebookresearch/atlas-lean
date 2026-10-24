---
article_id: af_9ead0a6cd572de4f66ba6de6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.TranscendenceWanted.gelfondSchneider_complex_exp
---

# Gelfond Schneider complex exp

The every-value complex form of Gelfond–Schneider. If `a` and `b` are algebraic, `a ≠ 1`,
`b` is not rational, and `z` is any logarithm of `a`, then `exp (b * z)` is transcendental.
The hypothesis `exp z = a` already implies `a ≠ 0`. Taking
`z = log a + n * (2 * π * I)` recovers every integer-indexed logarithm branch.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.GelfondSchneider](../../../../../sources/v2/MathlibExt.md)
- A. O. Gelfond, *Sur le septième problème de Hilbert* (1934), and T. Schneider, *Transzendenzuntersuchungen periodischer Funktionen I. Transzendenz von Potenzen*, J. Reine Angew. Math. 172 (1935), 65–69, DOI 10.1515/crll.1935.172.65. Explicit arbitrary- and principal-branch applications occur in arXiv:2311.11127v1, arXiv:2607.23662v1, and arXiv:2608.17545v1. The Lean formalization in arXiv:2603.24823v1 states only the principal `Complex.cpow` value; this declaration records the arbitrary-logarithm form.
