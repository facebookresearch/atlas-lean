# Access Region

The array-like region addressed by an ordinary access attempt.

The backing constructor argument is observed at the temporary payload access
itself.  Encoding it in the region prevents a temporary event from silently
omitting the backing state.  Pending-stack `Array.push` is not a
`pendingRuns` access; only indexed reads and writes use that constructor.
