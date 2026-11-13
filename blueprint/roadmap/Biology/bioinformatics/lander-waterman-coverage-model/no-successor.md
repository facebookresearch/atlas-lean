# Read with no successor

Read `j` has no successor when no other read starts in the `L - 1` positions after it,
`starts j + 1, …, starts j + L - 1 (mod G)` (reads starting at the same position are not
successors of each other). In Lander and Waterman's terms such a read is counted as ending
an island, but several no-successor reads can lie in one island, so this is not the island
count.
