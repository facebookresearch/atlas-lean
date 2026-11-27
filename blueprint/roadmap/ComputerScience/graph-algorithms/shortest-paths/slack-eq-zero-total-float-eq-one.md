# Zero slack at both endpoints does not make an activity critical

In the project network
with events `0` (the source `s`), `1` and `2` (the sink `t`) and arcs `s → t`, `s → 1` and
`1 → t` (arcs `0`, `1` and `2`), each of real duration `1`, the endpoints `s` and `t` of the arc
`s → t` both have slack `LS - ES = 0` (`latestStart`, `earliestStart`), but the total float
(`totalFloat`) of the arc `s → t` is `1`, not `0`.
