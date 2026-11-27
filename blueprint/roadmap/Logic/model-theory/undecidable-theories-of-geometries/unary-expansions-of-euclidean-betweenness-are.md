# Unary expansions of Euclidean betweenness are Π¹₁-hard

For every n ≥ 2, the first-order theory of all expansions of (ℝⁿ, β) by one unary predicate is Π¹₁-hard; in particular the monadic Π¹₁-theory of (ℝⁿ, β) is not arithmetical.

**Theorem (Kuusisto, Meyers and Virtema).** Let $n \ge 2$. The first-order theory of the [unary expansion class](affine-betweenness-structures.md) $\mathcal E(\mathbb R^n, \beta)$ of the Euclidean betweenness structure is $\Pi^1_1$-hard. Consequently the monadic $\Pi^1_1$-theory of $(\mathbb R^n, \beta)$, the set of sentences $\forall P\,\varphi$ with $\varphi$ first-order in $\{\beta, P\}$ true in $(\mathbb R^n, \beta)$, is not arithmetical (Corollary 4.17).

This refutes a conjecture of Aiello and van Benthem.

## Depends on

- [Affine betweenness structures](affine-betweenness-structures.md)

## Proof depends on

None.

## Expansion

The proof follows that of the [$\Sigma^0_1$-hardness theorem](unary-expansions-of-planar-betweenness-are.md), interpreting labeled recurrence grids instead of supergrids (Lemma 4.14), and reduces the complement of Harel's recurrent tiling problem, which is $\Sigma^1_1$-complete: does a tile set tile the quadrant with a designated tile occurring infinitely often in the first column?

## Sources

- A. Kuusisto, J. Meyers and J. Virtema, "Undecidable First-Order Theories of Affine Geometries", *Logical Methods in Computer Science* 9(4), 2013, paper 26, pp. 1–23, <https://doi.org/10.2168/LMCS-9(4:26)2013>; numbers from arXiv:1310.8200v3, <https://arxiv.org/abs/1310.8200v3>: Section 4: Lemma 4.14, Theorem 4.16 and Corollary 4.17; Theorem 2.3 (recurrent tiling).
- D. Harel, "Effective transformations on infinite trees, with applications to high undecidability, dominoes, and fairness", *Journal of the ACM* 33(1):224–248, 1986, <https://doi.org/10.1145/4904.4993>: $\Sigma^1_1$-completeness of the recurrent tiling problem, as recalled in Section 2.2 of the version of the first source read.
