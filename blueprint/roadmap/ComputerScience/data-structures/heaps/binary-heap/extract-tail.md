# Removing the root of a nonempty binary min-heap

Let $h$ be a binary min-heap over a
linearly ordered type whose level-order array is nonempty. If the array has exactly one entry,
the result is the empty heap. Otherwise the last entry of the array replaces the root, the array
shrinks by one, and the result is the heap obtained by sifting this entry down from the root.
