# Rebuilding an internal node after insertion

For minimum degree $t$, a separator list $K$
and a child list $C$, the result is the internal node with separators $K$ and children $C$, kept
as a single tree when $K$ has at most $2t - 1$ keys, and otherwise split by node splitting into
two nodes and a promoted median key.
