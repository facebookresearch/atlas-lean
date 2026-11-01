---
article_id: af_46ab44def0221ceb625a058d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.BilinearFormRankWanted.bilinFormRank_basis_independent
---

# Bilin Form Rank basis independent

The rank of a bilinear form does not depend on the choice of basis.

Proof: Express one Gram matrix as a two-sided change-of-basis product. The two matrix-rank
multiplication inequalities give both rank inequalities, hence equality.

## Depends on

- [Bilin Form Rank](bilin-form-rank.md)

## Proof depends on

- [Rank to Matrix eq rank to Matrix](rank-to-matrix-eq-rank-to-matrix.md)
- [Bilin Form Rank eq matrix rank](bilin-form-rank-eq-matrix-rank.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.BilinearFormRank](../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space / Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989), Chapter III.
