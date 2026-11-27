# Latest start of an event

For a project network `tail head : E → V` with arc durations
`d`, source `s` and sink `t`, the latest start of the event `v` is the project length
`L = ℓ(s, t)` minus the duration of a longest walk from `v` to `t`,
`LS(v) = ℓ(s, t) - ℓ(v, t)` (`longestDuration`).
