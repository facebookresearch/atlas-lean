# Truncated suffix of a suffix-array row

Let $A$ be a list of natural numbers (a precomputed suffix array), $s$ a list over a linear order
and $m, r \in \mathbb{N}$. The key of row $r$ is the list of the first $m$ letters (all of them if
there are fewer) of the suffix of $s$ starting at the entry of $A$ at position $r$, where that
entry is taken to be $0$ if $r$ is not a position of $A$.
