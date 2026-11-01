---
article_id: af_f4ab0f86b71bd9a705477391
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.lovasz_weak_perfect_graph_general
---

# Lovasz weak perfect graph general

Weak perfect graph theorem without decidable equality: `G` perfect iff `Gᶜ` perfect.
General version of `lovasz_weak_perfect_graph`; the `DecidableEq` instance needed by
the internal finset argument is obtained locally via `classical`.

## Depends on

- [Is Perfect](is-perfect.md)

## Proof depends on

- [Perf Ineq](perf-ineq.md)
- [Perfect implies ineq](perfect-implies-ineq.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.PerfectGraph](../../../../../../../sources/v2/MathlibExt.md)
