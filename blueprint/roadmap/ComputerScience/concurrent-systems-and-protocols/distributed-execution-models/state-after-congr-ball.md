# Locality in the LOCAL model

After $k$ rounds, the state of a node $v$ depends only on its ball of radius $k$. Let $A$ be an [algorithm in the LOCAL model](local-algorithm.md), $G$ and $G'$ simple graphs on the same finite set $V$ of nodes, $\mathrm{id}, \mathrm{id}' : V \to \mathbb{N}$, $x, x' : V \to I$, $v \in V$ and $k \in \mathbb{N}$. Suppose that $\mathrm{id}(u) = \mathrm{id}'(u)$ and $x(u) = x'(u)$ for every node $u$ at distance at most $k$ from $v$ in $G$, and that every node at distance less than $k$ from $v$ in $G$ has the same neighbours in $G$ as in $G'$. Then the [state of $v$ after $k$ rounds](state-after.md) of $A$ on $G$ with identifiers $\mathrm{id}$ and inputs $x$ equals its state after $k$ rounds of $A$ on $G'$ with identifiers $\mathrm{id}'$ and inputs $x'$.

Distances are taken in $G$; a node in another connected component is at infinite distance. Nothing is assumed about the edges between two nodes at distance at least $k$ from $v$.

**Proof.** By induction on $k$, for all nodes $v$ at once. The case $k = 0$ is the hypothesis at $v$. For $k + 1$, the node $v$, at distance $0 < k + 1$, has the same neighbours in $G$ and $G'$ and the same identifier, which addresses their messages to it; its own state after $k$ rounds agrees by induction; and so do the states after $k$ rounds of its neighbours $u$, since a node at distance at most $k$ (or less than $k$) from $u$ is at distance at most $k + 1$ (or less than $k + 1$) from $v$.

## Sources

- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992: §2, which observes that at time $t$ a processor knows the identifiers of the nodes at distance at most $t$ and the edges among them, except those whose two endpoints are both at distance exactly $t$.
