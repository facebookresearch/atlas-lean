# Sentinel search changes only the sentinel's key

Let $s$ be the sentinel of some list of
data nodes that a store circularly represents, and let $k$ be a key. In the store returned by
sentinel search for $k$, the cell $s$ holds the original sentinel node with its key replaced by
$k$ and its satellite data and next and prev links unchanged, and every cell $z \ne s$ holds
exactly what it held in the input store.
