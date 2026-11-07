# One level of skip-list search

Let $k$ be a search key, $i$ a zero-based level and $L$
a list of skip-list nodes. Let $P$ be the longest prefix of $L$ whose nodes all have keys less
than $k$. If some node of $P$ has tower height greater than $i$ (so it is visible at level
$i$), advancing at level $i$ returns the part of $L$ after the last such node; otherwise it
returns $L$ unchanged.

The returned suffix is the window that every lower level continues to scan.
