---
article_id: af_b9f7a62cd4d545b989dedf53
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hardy_inequality
---

# Hardy Inequality

Hardy's inequality (series form): for a nonnegative `p`-summable sequence
with `p > 1`, the series of `p`-th powers of the partial averages
`A n = (∑ i in Finset.range (n + 1), a i) / (n + 1)` is bounded by
`(p / (p - 1)) ^ p` times the series of `p`-th powers of `a`.

Proof: Elliott's finite telescoping argument is combined with Young's and Hölder's inequalities,
following E. B. Elliott (1926) as presented in Hardy--Littlewood--Pólya, *Inequalities*,
Theorem 326.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Series.HardyInequality](../../../../../sources/v2/MathlibExt.md)
- G. H. Hardy, *Note on a theorem of Hilbert*, Mathematische Zeitschrift 6 (1920), 314-317 (statement hardy-ineq-s1): the discrete series form with constant `(p / (p - 1)) ^ p` for `p > 1`.
