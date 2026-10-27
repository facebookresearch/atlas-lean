---
article_id: af_79722c5c998cdbd544f96c86
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.lunnon_fixed_polycube_dimension_decomposition
---

# Lunnon fixed polycube dimension decomposition

Lunnon's dimension-decomposition formula for fixed polycubes, corrected
domain `1 < n`: `A_d(n) = ∑_{i=1}^{n-1} C(d,i) * DX(n,i)`.

The `1 < n` restriction is required because the printed display omits its
`n`-domain and is false at `n = 1`: the one-cell polycube is zero-dimensional,
so it is counted by the `i = 0` term, which the sum over `Ico 1 n` excludes.
On `n > 1` the `i = 0` term vanishes by `DX(n,0) = 0`, making the omission
valid exactly on this domain. No claim is made for `n = 1`.

## Depends on

- [Fixed Polycube Count](fixed-polycube-count.md)
- [Proper Fixed Polycube Count](proper-fixed-polycube-count.md)

## Proof depends on

- [Face Adjacent](face-adjacent.md)
- [Fixed Polycube](fixed-polycube.md)
- [Is Canonical Cells](is-canonical-cells.md)
- [Is Polycube Cells](is-polycube-cells.md)
- [Lattice Cell](lattice-cell.md)
- [Proper Dimension](proper-dimension.md)
- [Proper Fixed Polycube](proper-fixed-polycube.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.LunnonDimensionDecomposition](../../../../../../../sources/v2/MathlibExt.md)
- Sebastian Luther and Stephan Mertens, *The Perimeter of Proper Polycubes*, Journal of Integer Sequences 20 (2017), Article 17.9.5, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Mertens/mert4.tex>: Lunnon's classical formula `eq:lunnon-a`, lines 172–175, with sum `i = 1, …, n-1` and factor `C(d,i)`; `DX` notation and the at-most-`n-1` dimensions bound, lines 163–166. Original: W. F. Lunnon, *Counting multidimensional polyominoes*, Comput. J. 18 (1975), 366–367. `DX(n,0) = 0` for `n > 1` from Asinowski–Barequet–Barequet–Rote, JIS 15 (2012), Article 12.8.4, line 978, <https://cs.uwaterloo.ca/journals/JIS/VOL15/Barequet/barequet2.tex>.
