---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Karger.successProb_ge
---

# Success Prob ge

Karger's bound: on a valid multigraph with `n ≥ 2` vertices and minimum cut size `k`, the
contraction process returns `k` with probability at least `2 / (n (n - 1))`.

## Depends on

- [Is Min Cut](is-min-cut.md)
- [State](state.md)
- [Valid](valid.md)
- [Success Prob](success-prob.md)

## Proof depends on

- [Is Cut](is-cut.md)
- [Card mul le two mul edges](card-mul-le-two-mul-edges.md)
- [Contract](contract.md)
- [Cut Size](cut-size.md)
- [Is Min Cut contract](is-min-cut-contract.md)
- [Success Prob nonneg](success-prob-nonneg.md)
- [Valid contract](valid-contract.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Random.KargerMinCut](../../../../../../../sources/v2/CSLibExt.md)
