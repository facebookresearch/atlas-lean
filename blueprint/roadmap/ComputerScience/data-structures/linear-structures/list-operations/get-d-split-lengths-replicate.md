# Splitting a list at a repeated width

Let $w$, $m$ and $i$ be natural numbers with $i < m$, and $L$ a list. Split $L$ at $m$ copies of
the length $w$ (consecutive chunks of $w$ elements cut from the front of $L$, shorter once $L$
runs out). Then the chunk at position $i$ (a default list is returned for positions out of range)
is the list of the first $w$ elements, or all of them if there are fewer, of the list obtained
from $L$ by dropping its first $i w$ elements.
