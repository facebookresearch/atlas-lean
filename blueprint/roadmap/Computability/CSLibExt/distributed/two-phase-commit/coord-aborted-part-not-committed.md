---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.TwoPhaseCommit.coord_aborted_part_not_committed
---

# Coord aborted part not committed

AC1 between the coordinator and a participant: an aborted coordinator has
no committed participant.

## Depends on

- [Coord State](coord-state.md)
- [Part State](part-state.md)
- [Reachable](reachable.md)
- [State](state.md)

## Proof depends on

- [Inv](inv.md)
- [Inv reachable](inv-reachable.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.TwoPhaseCommit](../../../../../sources/v2/CSLibExt.md)
