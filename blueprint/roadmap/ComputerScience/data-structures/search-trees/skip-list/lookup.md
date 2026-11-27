# Skip-list lookup

The lookup of a key $k$ in a skip list computes the search window for
$k$, the suffix of the bottom-level nodes reached by descending from the highest level to level
$0$, and returns the value of the first node in the window whose key is $k$, or no value if the
window has no such node.
