---
article_id: af_1f384115b93ecee236f9b125
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bell_turan_identity
---

# Bell Turan Identity

Turán-type log-convexity identity for the Bell numbers.

Math notes: every summand is nonnegative (squared factor `(k - 2*j)^2`), so the
identity exhibits `B_{n-1} B_{n+1} - B_n^2` as a series with nonnegative terms,
refining Engel's inequality `B_n^2 ≤ B_{n-1} B_{n+1}` to a strict inequality.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BellTuranIdentity](../../../../../../sources/v2/MathlibExt.md)
- Horst Alzer, "On Engel's Inequality for Bell Numbers," Journal of Integer Sequences 22 (2019), Article 19.7.1, Theorem with Equation (E3), lines 114–120, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Alzer/alzer6.tex>.
