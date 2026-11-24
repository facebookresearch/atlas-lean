# Merge Getmem reused storage valid

The reuse branch leaves the entire state unchanged while preserving live,
invariant-valid storage with enough logical capacity for the request.  The
`Live` premise deliberately rules out stale-capacity reuse after release.
