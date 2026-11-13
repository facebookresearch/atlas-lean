# Exact round count for traversing a terminal frontier

If every frontier occurrence is terminal, exactly `2 * length - 1` rounds process
the tree below `s`, preserving the tail `r` and prepending its reversed frontier to `out`.
The terminal-frontier hypothesis is essential: a depth cut may contain branching states.
