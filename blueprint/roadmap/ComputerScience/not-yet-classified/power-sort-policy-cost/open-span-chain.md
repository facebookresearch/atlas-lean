# Open Span Chain

A forest tiles the suffix from `start` to the end of `input` with positive,
in-bounds spans.  The recursive endpoint is also the next root's base, so this
single relation exposes start, adjacency, containment, and exact suffix
coverage without hiding any of them behind list arithmetic.
