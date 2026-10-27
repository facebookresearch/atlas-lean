---
article_id: af_33fe6c8b179387c05bdfaca6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: PSDMatrix.isPSD_iff_exists_transpose_mul_self_rect
---

# Lemma 8 (PSD Matrix Decomposition)

$M$ is PSD if and only if there exists a matrix $A$ such that $M = A^\top A$. Note that $A$ can be $(n \times k)$ for any $k$, and that it need not be square. Importantly, note that $A$ is not unique.

## Depends on

- [Definition 6 (Lecture 2, Section 3.3)](011-definition-6.md)

## Proof depends on

- [Proposition 2 (Lecture 1, Section 2)](../../lecture-1/002-proposition-2.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 2, Section 3.3](../../../../../../sources/v1/AnAlgorithmistsToolkit.md)
