# Running time of the edit distance algorithm

For lists $s$ and $t$ over a type with a
Boolean equality test, the total number of events charged by the edit distance algorithm on $s$
and $t$, that is its cell transitions plus its reconstruction steps, equals
$(|s| + 1)(|t| + 1) + k$, where $k$ is the length of the edit script it returns.
