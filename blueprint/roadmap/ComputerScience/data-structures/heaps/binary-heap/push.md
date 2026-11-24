# Insertion into a binary min-heap

To insert a value $x$ into a binary min-heap $h$, append
$x$ at the end of the level-order array of $h$ and sift it up from its index (the old length of
the array), repeatedly swapping it with its parent while it is smaller. The result is again a
binary min-heap.
