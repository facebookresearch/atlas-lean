---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Concurrency.Banker.System.safe_iff_safe_erase
---

# Safe iff safe erase

Once a pending process that fits has finished, safety of the remaining
processes is equivalent to safety of all of them.

## Depends on

- [System](system.md)
- [Safe](safe.md)
- [Need](need.md)

## Proof depends on

- [Safe Seq](safe-seq.md)
- [Erase](erase.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Banker](../../../../../sources/v2/CSLibExt.md)
