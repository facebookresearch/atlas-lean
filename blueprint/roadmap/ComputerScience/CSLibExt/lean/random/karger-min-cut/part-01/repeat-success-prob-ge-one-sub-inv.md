---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Karger.repeatSuccessProb_ge_one_sub_inv
---

# Repeat Success Prob ge one sub inv

With `⌈log₂ n⌉ · n (n - 1) / 2` runs (or more), the minimum cut size is found with probability
at least `1 - 1 / n` (Karger's algorithm succeeds with high probability after `O(n² log n)`
runs).

## Depends on

- [Is Min Cut](is-min-cut.md)
- [State](state.md)
- [Valid](valid.md)
- [Repeat Success Prob](repeat-success-prob.md)

## Proof depends on

- [Amplification with high probability](repeat-success-prob-ge.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Random.KargerMinCut](../../../../../../../sources/v2/CSLibExt.md)
