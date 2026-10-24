---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.Karger.repeatSuccessProb_ge
---

# Amplification with high probability

**Amplification with high probability.** Repeating the algorithm `c · n (n - 1) / 2` times (or
more) finds the minimum cut size with probability at least `1 - (1/2)^c`.

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
