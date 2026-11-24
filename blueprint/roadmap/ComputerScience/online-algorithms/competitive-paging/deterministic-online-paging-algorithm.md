# Deterministic online paging algorithm

Let $\alpha$ be a type of pages and $k \in \mathbb{N}$. A deterministic online paging algorithm
with cache size $k$ on $\alpha$ is a state machine: a set of states, an initial state, a cache map
assigning to each state $q$ a list of pages with at most $k$ entries (the pages cached in $q$), and
a step map giving the state reached from a state $q$ by serving a request for a page $p$. Its moves
need not be legal transitions of a cache (the requested page need not be cached afterwards, and
pages may change without a miss); lower bounds proved for such machines hold for every
deterministic online pager.
