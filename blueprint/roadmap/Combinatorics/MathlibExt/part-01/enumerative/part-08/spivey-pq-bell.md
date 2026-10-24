---
article_id: af_f61c7301c7fbd810ea636a3c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.spivey_pq_bell
---

# Spivey PQBell

(p, q)-deformation of Spivey's Bell number formula: the `(p, q)`-Bell value
`tildeB (n + m) 1` expands as the double sum over `k ≤ m` and `j ≤ n` of
`C(n,j) * tildeS m k * bracket k ^ (n - j) * q ^ (j * k) * tildeB j (p ^ (n + m - j))`.

Proof: We formalize the operator proof around equations `eq1`, `eq2'`, `eq4`, `meq`,
`pqexpn`, and `lasteq` in Oussi's paper, using formal power series in place of convergent series.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.SpiveyPQBell](../../../../../../sources/v2/MathlibExt.md)
- L. Oussi, *A (p,q)-Deformed Recurrence for the Bell Numbers*, Journal of Integer Sequences 23 (2020), Article 20.5.2, main theorem equation `lasteq`, lines 214-220, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Oussi/oussi5.tex>.
