---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Concurrency.Banker.System.safetyCheck
---

# Safety Check

The banker's safety algorithm: reject a pending list with repetitions,
then at most one round per pending process.

## Depends on

- [System](system.md)

## Proof depends on

- [Safety Check Aux](safety-check-aux.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Banker](../../../../../sources/v2/CSLibExt.md)
