---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Distributed.TwoPhaseCommit.committed_imp_all_voted_yes
---

# Validity

**Validity** (AC3): if a participant commits, every participant voted
yes (it is prepared or committed); the coordinator decided commit by
`part_committed_coord_committed`.

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
