---
article_id: af_3fbfb70fd1d45ee84c02873c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.randomlyPermute_prefix_probability
---

# Randomly Permute prefix probability

Every injective labelled prefix has mass `(n - k)! / n!` in the actual run.
The finite sum uses the proved complete independent-history mass `1 / n!`;
empty and full prefixes are included, with no new probability-event wrapper.

## Depends on

- [Randomly Permute](../basic/randomly-permute.md)

## Proof depends on

- [Randomly Permute time](../basic/randomly-permute-time.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Random.RandomlyPermute.Probability](../../../../../../../sources/v2/CSLibExt.md)
