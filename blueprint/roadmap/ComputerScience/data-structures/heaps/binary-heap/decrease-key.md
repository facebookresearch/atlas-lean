# Decrease-key in a binary min-heap

Given a binary min-heap $h$ over a linearly ordered
type, with level-order array $a$, an index $i < |a|$ and a value $x \le a_i$, decrease-key returns
the heap whose array is obtained from $a$ by replacing the entry at position $i$ with $x$ and then
sifting position $i$ up, repeatedly swapping the entry with its parent while it is strictly
smaller than the parent.
