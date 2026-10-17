---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Concurrency.Banker.System.safetyCheckAux
---

# Safety Check Aux

The banker's safety algorithm with explicit fuel: let some pending process
whose remaining need fits in the free resources finish, release its
allocation, and repeat; succeed when no process is left.

## Depends on

- [System](system.md)

## Proof depends on

- [Need](need.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Concurrency.Banker](../../../../../sources/v2/CSLibExt.md)
