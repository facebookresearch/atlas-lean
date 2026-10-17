---
article_id: af_4cf628b4a6f2c422fe4fc729
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.catalan_not_perfect_power
---

# Catalan Perfect Power

For all `n ≥ 2`, the `n`-th Catalan number is never a perfect power.

The paper includes the Checcoli–D'Adderio proof for completeness
(lines 152–156): small cases checked directly, and for `n ≥ 6` a
Ramanujan prime `p ∈ [n+2, 2n)` divides `C_n` exactly once, so no
`C_n = m ^ k` with `k ≥ 2` is possible. Spot-checked for `n = 2..60`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CatalanPerfectPower](../../../../../../sources/v2/MathlibExt.md)
- Nathaniel Benjamin, Grant Fickes, Eugene Fiorini, Edgar Jaramillo Rodriguez, Eric Jovinelly, and Tony W. H. Wong, "Primes and Perfect Powers in the Catalan Triangle," Journal of Integer Sequences 22 (2019), Article 19.7.6, Theorem [Checcoli–D'Adderio] (label `c_nn not power`), lines 148–150, https://cs.uwaterloo.ca/journals/JIS/VOL22/Fiorini/fiorini3.tex
