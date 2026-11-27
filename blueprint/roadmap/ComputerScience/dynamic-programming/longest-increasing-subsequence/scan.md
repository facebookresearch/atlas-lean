# The patience scan preserves the invariant

Let $P$ be a list and $t$ an array of tails over
a linear order such that the patience sorting invariant holds for $P$ and the entries of $t$. Then
for every list $xs$, the invariant holds for $P$ followed by $xs$ and the entries of the array
returned by the patience scan of $xs$ from $t$.
