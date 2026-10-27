---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Hierholzer.udeg_erase
---

# Udeg erase

Hierholzer's algorithm on an undirected edge list, from `s`. -/
def uhierholzer (E : List (V × V)) (s : V) : TimeM ℕ (List V) := do
  let r ← uvisit (E.length + 1) s E []
  pure r.1

/-! ## Degrees

## Depends on

- [Udeg](udeg.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Graph.HierholzerUndirected](../../../../../../sources/v2/CSLibExt.md)
