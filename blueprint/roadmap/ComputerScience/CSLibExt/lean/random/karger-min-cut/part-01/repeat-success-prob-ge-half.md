---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Karger.repeatSuccessProb_ge_half
---

# Repeat Success Prob ge half

Repeating the algorithm `n (n - 1) / 2` times (or more) and keeping the best answer finds the
minimum cut size with probability at least `1 / 2`.

## Depends on

- [Is Min Cut](is-min-cut.md)
- [State](state.md)
- [Valid](valid.md)
- [Repeat Success Prob](repeat-success-prob.md)

## Proof depends on

- [Success Prob](success-prob.md)
- [Success Prob ge](success-prob-ge.md)
- [Success Prob le one](success-prob-le-one.md)
- [Success Prob nonneg](success-prob-nonneg.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Random.KargerMinCut](../../../../../../../sources/v2/CSLibExt.md)
