# Lookup with cost

The costed lookup of a key $k$ in a tree with keys in a linearly
ordered type returns a possibly absent value together with a natural number counting the
visited nodes. On the empty tree it returns no value and cost $0$. At a node with key $r$ and
value $v$, if $k < r$ it returns the result of the costed lookup of $k$ in the left subtree
with cost increased by $1$; if $r < k$ it does the same with the right subtree; otherwise it
returns $v$ with cost $1$.
