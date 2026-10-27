---
article_id: af_439a14cb307d926a40ef93e2
declaration: def
origin: cited
statement: formalized
lean: Matrix.lowerToeplitz
---

# Lower Toeplitz

Lower-triangular Toeplitz matrix over `ℕ × ℕ`: given a sequence `a`,
the `(i, j)` entry is `a (i - j)` when `j ≤ i`, and `0` otherwise. In
particular the matrix is constant on each subdiagonal and vanishes strictly
above the main diagonal.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.LowerToeplitz](../../../../../../sources/v2/MathlibExt.md)
- Ming-Jian Ding and Jiang Zeng, "Some New Results on the Minuscule Polynomials of Type A," Journal of Integer Sequences 28 (2025), lines 640-653. URL: `https://cs.uwaterloo.ca/journals/JIS/VOL28/Zeng/zeng26.tex`. Full TeX SHA-256: `2a5a8d59641da82808dae4aea4c6583f460dd36bc175d9dce912a265a5ce7a1a`. Exact source-span SHA-256 including terminal LF: `63b54ec23b76494d198b28837c6622e4bbe92e064580f13cde8f3d1523ac28e3`. Grounded concept: `jis_grounded_6e7ca1c0ec8f4d9d675959b3`.
