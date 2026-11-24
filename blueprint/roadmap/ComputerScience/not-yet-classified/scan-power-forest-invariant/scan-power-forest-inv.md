# Scan Power Forest Inv

The scan-carried historical certificate for an open merge forest.

`basekeys_eq` and `listlen_eq` are the exact machine/input frame.  `aligned`
keeps forest roots and pending runs in lockstep; unlike a span-only matching
predicate, it retains each root's internal PowerSort validity and the missing
heap edge from the outgoing pending power into that root.
