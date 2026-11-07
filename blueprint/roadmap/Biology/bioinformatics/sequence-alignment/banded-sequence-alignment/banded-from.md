# Band check from a starting offset

Let $w \in \mathbb{N}$ be a band width. For natural
numbers $i$, $j$ and an alignment $A$, the band check of $A$ with width $w$ from offset $(i, j)$
is true exactly when every prefix $P$ of $A$ (including the empty prefix and $A$ itself)
satisfies $|(i + p) - (j + q)| \le w$, where $p$ and $q$ are the numbers of columns of $P$
whose first, respectively second, entry is present.
