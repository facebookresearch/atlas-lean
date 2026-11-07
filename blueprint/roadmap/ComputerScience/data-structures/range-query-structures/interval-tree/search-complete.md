# Completeness of interval-tree search

Let $T$ be an interval tree whose cached height, size
and maximum high endpoint are exact at every node, and whose low endpoints respect the search
order (at every node, low endpoints in the left subtree are at most the node's, and those in the
right subtree at least the node's). If some entry stored in $T$ has an interval that overlaps the
query interval $Q$ (each interval's low endpoint is at most the other's high endpoint), then
searching $T$ for $Q$ returns some entry.
