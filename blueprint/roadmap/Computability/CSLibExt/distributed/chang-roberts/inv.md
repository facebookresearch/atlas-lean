---
declaration: structure
origin: cited
statement: formalized
lean: Cslib.Distributed.ChangRoberts.Inv
---

# Inv

The invariant: every process strictly between the origin of a message and
its current position has a smaller identifier, and a leader's identifier is
larger than every other.

## Depends on

- [State](state.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.ChangRoberts](../../../../../sources/v2/CSLibExt.md)
