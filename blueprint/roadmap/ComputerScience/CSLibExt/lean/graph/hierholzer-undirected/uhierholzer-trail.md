---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.uhierholzer_trail
---

# Uhierholzer trail

When exactly `s` and `t` have odd degree (none when `s = t`), the result is a walk from `s`
to `t` whose steps, as unordered pairs, are a sub-multiset of the edges: no edge is traversed
twice.

## Depends on

- [Even Except](even-except.md)
- [Uhierholzer](uhierholzer.md)
- [Usym](usym.md)
- [Walk Edges](../hierholzer/part-01/walk-edges.md)

## Proof depends on

- [Udeg](udeg.md)
- [Uvisit](uvisit.md)
- [Uvisit spec](uvisit-spec.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.HierholzerUndirected](../../../../../../sources/v2/CSLibExt.md)
