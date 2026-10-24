---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Distributed.ChangRoberts.deliver
---

# Deliver

Process `k` receives the oldest message in its channel: forward a larger
identifier, discard a smaller one, become leader on its own.

## Depends on

- [State](state.md)

## Proof depends on

- [Succ](succ.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Distributed.ChangRoberts](../../../../../sources/v2/CSLibExt.md)
