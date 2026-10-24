---
article_id: af_b154659c88317e61a320222c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.young_reverse_multiple_carry_path_iff
---

# Young reverse multiple carry path iff

Carry recurrence for reverse multiples: a `(g, k)` reverse multiple in
little-endian base-`g` digits holds exactly when there is a unique carry
sequence `r` with `r 0 = 0`, `r n = 0`, every carry below `k`, and the column
equations `k * a i + r i = a (n - 1 - i) + r (i + 1) * g`; `r (i + 1)` is the
source's `r_i`. The Young graph `H(g, k)`, its paths and the even/odd pivot-node
correspondence of Young's theorem (`thm:youngsthm`, lines 192–196) are not
formalized here.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Young reverse multiple carry path iff general](young-reverse-multiple-carry-path-iff-ge.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Digits.YoungReverseMultipleCarryPath](../../../../../../sources/v2/MathlibExt.md)
- L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer Sequences 18 (2015), Article 15.9.7, subsection `subsec:eqtns`, lines 128–154 (the column equations for `kN = Reverse_g(N)`, Young's bound `r_i ≤ k - 1`, and equation `eq:rmdig`), <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>. It follows from `young_reverse_multiple_carry_path_iff_general`; the hypotheses `hfirst` and `hlast` (and `hn`, which only serves to state them) are unused and keep the source's shape. Proves `Wanted` entry `young_reverse_multiple_carry_path_iff`.
