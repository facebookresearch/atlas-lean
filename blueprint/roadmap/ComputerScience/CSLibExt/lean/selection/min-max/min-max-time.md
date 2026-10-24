---
article_id: af_9c5b5916e0aef89a7e032f07
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.minMax_time
---

# Min Max time

The same run uses exactly `ceil (3 * length / 2) - 2` comparisons when nonempty.
This counts element-order decisions, not full RAM instructions or comparator bit complexity.

## Depends on

- [Min Max](min-max.md)

## Proof depends on

- [Min Max nil](min-max-nil.md)
- [Min Max time even](min-max-time-even.md)
- [Min Max time odd](min-max-time-odd.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Selection.MinMax](../../../../../../sources/v2/CSLibExt.md)
