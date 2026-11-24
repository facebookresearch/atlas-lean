# Extracting the minimum of a binary min-heap

For a binary min-heap $h$ over a linearly
ordered type, extraction returns nothing when the level-order array of $h$ is empty. Otherwise it
returns the root entry (the first entry of the array) together with the heap obtained from $h$ by
removing its root and restoring heap order.
