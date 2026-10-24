---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.TwoPhaseCommit.coord_committed_imp_all_voted_yes
---

# Validity

**Validity** (AC3) for the coordinator: if it commits, every participant
voted yes (it is prepared or committed).

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
