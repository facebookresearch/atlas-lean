---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.TwoPhaseCommit.atomicity
---

# Atomicity

**Atomicity** (AC1), between participants: no reachable state has one
participant committed and another aborted.

## Depends on

- [Part State](part-state.md)
- [Reachable](reachable.md)
- [State](state.md)

## Proof depends on

- [Coord State](coord-state.md)
- [Inv](inv.md)
- [Inv reachable](inv-reachable.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.TwoPhaseCommit](../../../../../sources/v2/CSLibExt.md)
