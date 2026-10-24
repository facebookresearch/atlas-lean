---
article_id: af_c40443b12c34399b70d0e1f1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SpaceCurves.gram_schmidt_orthonormalization
---

# Lemma 5.1 (Gram-Schmidt orthogonalization)

Let $(v_{1}, \ldots, v_{k})$ be linearly independent vectors. There are unique orthonormal vectors $(e_{1}, \ldots, e_{k})$ of the form $e_{i} = \sum_{j \leq i} f_{ij} v_{j}$ where $f_{ii} > 0$. Note that in particular, each $(e_{1}, \ldots, e_{i})$ spans the same subspace as $(v_{1}, \ldots, v_{i})$. An explicit inductive formula is $e_{i} = \frac{v_{i} - \langle v_{i}, e_{1}\rangle e_{1} - \cdots - \langle v_{i}, e_{i-1}\rangle e_{i-1}}{\|v_{i} - \langle v_{i}, e_{1}\rangle e_{1} - \cdots - \langle v_{i}, e_{i-1}\rangle e_{i-1}\|}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.950 Differential Geometry (Fall 2008), Chapter 1, Lecture 5](../../../../../../sources/v1/DifferentialGeometry.md)
