---
article_id: af_e02485d29c1e26f90f19155c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.perfect_composition_iff_symbolic_parts_perm_perfect_partition
---

# Perfect composition iff symbolic parts perm perfect partition

A symbolic part `(a, u)` denotes a run of `u` copies of the positive part `a`.

A composition is perfect when its parts contain exactly one composition (sublist) of
every smaller positive integer. The theorem says a composition of `n` is perfect iff
its symbolic parts permute those of a perfect partition of `n` (written with strictly
increasing part sizes).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Perfect composition iff symbolic parts perm perfect partition general](perfect-composition-iff-symbolic-parts-p.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PerfectCompositions](../../../../../../../sources/v2/MathlibExt.md)
- Augustine O. Munagi, "Perfect Compositions of Numbers," Journal of Integer Sequences 23 (2020), Article 20.5.1, Theorem 1 (label `thm1`), lines 138–140, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Munagi/munagi13.tex>.
