# Descending Scan Traced next smaller priority

Conditioned equation pinning comparator priority: a true
`next < previous` answer selects the equality-block reversal/recursive arm,
independently of the reverse comparison's value.  Comparator calls are not
access-trace events, so this is a branch equation rather than a trace claim.
