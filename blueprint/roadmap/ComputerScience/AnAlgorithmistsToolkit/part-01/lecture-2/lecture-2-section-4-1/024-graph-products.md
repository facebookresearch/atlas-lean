---
article_id: af_6e283bddc2c53309ffd5b2ce
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: GraphProductSpectrum.lapMatrix_boxProd_eigenvector
---

# Theorem 19 (Graph Products)

If $L_G$ has eigenvectors $v_1, \ldots, v_n$ with eigenvalues $\lambda_1, \ldots, \lambda_n$, and $L_H$ has eigenvectors $w_1, \ldots, w_k$ with eigenvalues $\mu_1, \ldots, \mu_k$, then $L_{G \times H}$ has, for all $1 \leq i \leq n$, $1 \leq j \leq k$, an eigenvector $z_{ij}(v,w) = x_i(v) y_j(w)$ of eigenvalue $\lambda_i + \mu_j$.

## Depends on

- [Definition 1 (Lecture 1, Section 2)](../../lecture-1/001-definition-1.md)
- [Definition 18](023-definition-18.md)

## Proof depends on

- [Lemma 1 (Edge Union)](../lecture-2-section-3-1/007-edge-union.md)
- [Lemma 3 (Disjoint Union)](../lecture-2-section-3-1/009-disjoint-union.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 2, Section 4.1](../../../../../../sources/v1/AnAlgorithmistsToolkit.md)
