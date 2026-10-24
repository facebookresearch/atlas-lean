---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.exists_isUEulerPath_iff
---

# Euler's theorem

**Euler's theorem**, algorithmic form: when every edge starts at a vertex reachable from `s`,
an Euler path from `s` to `t` exists iff exactly `s` and `t` have odd degree (every degree is even
when `s = t`), and then `uhierholzer E s` finds one.

## Depends on

- [Even Except](even-except.md)
- [Is UEuler Path](is-ueuler-path.md)
- [UReach](ureach.md)

## Proof depends on

- [Even Except of is UEuler Path](even-except-of-is-ueuler-path.md)
- [Uhierholzer](uhierholzer.md)
- [Euler paths](uhierholzer-is-ueuler-path.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.HierholzerUndirected](../../../../../../sources/v2/CSLibExt.md)
