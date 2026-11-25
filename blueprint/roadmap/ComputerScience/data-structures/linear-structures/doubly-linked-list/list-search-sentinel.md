# Search in a circular list with a sentinel

Let a store have cells indexed by
$\{0, \dots, m-1\}$, each empty or holding a node that carries a key, satellite data and optional
next and prev links, and let the cell $s$ be the sentinel of some list of data nodes that the
store circularly represents. Sentinel search for a key $k$ first overwrites the key of the
sentinel with $k$, keeping its satellite data and links, then starts at the successor of $s$ and
follows next links until it reaches a node whose key is $k$. It returns the modified store
together with that node, or no node if the scan stopped at $s$.

Only the sentinel key is overwritten, and its old key is not restored. The cost charges one unit
for the key write, one for initializing the cursor, one for each key comparison, one for each
advance past a mismatching node and one for the final test against $s$; reads and result
construction are free, and physical storage or bit operations are not counted.
