# Ready To Push

Facts about a newly discovered run before the caller's unconditional
`Array.push`.  The current pending stack still covers exactly `scanned`
entries, all of its runs are powered, and `newRun` is the adjacent nonempty
run just outside that stack.  Its stored `power` field is irrelevant, matching
the C push, which writes only base and length.  The exact-boundary predicate is
stated on the virtual post-push list, so it also pins the current top run's
stored power to the boundary with `newRun`.  No array-capacity premise is
present.
