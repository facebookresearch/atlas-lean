---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Concurrency.Banker.System.SafeSeq.erase
---

# Erase

Letting a member of a safe sequence finish first leaves the rest of the
sequence safe. This is why the greedy safety check is complete.

## Depends on

- [System](system.md)
- [Safe Seq](safe-seq.md)

## Proof depends on

- [Need](need.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Banker](../../../../../sources/v2/CSLibExt.md)
