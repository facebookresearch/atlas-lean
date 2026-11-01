---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.uhierholzer_isUEulerPath
---

# Euler paths

**Euler paths.** If exactly `s` and `t` have odd degree (none when `s = t`) and every edge
starts at a vertex reachable from `s`, the result is an Euler path from `s` to `t`.

## Depends on

- [Even Except](even-except.md)
- [Is UEuler Path](is-ueuler-path.md)
- [UReach](ureach.md)
- [Uhierholzer](uhierholzer.md)

## Proof depends on

- [Udeg](udeg.md)
- [Usym](usym.md)
- [Uvisit](uvisit.md)
- [Uvisit spec](uvisit-spec.md)
- [Walk Edges](../hierholzer/part-01/walk-edges.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.HierholzerUndirected](../../../../../../sources/v2/CSLibExt.md)
