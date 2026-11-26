# Locality of the output of a $t$-round algorithm

Let $A$ be an [algorithm in the LOCAL model](local-algorithm.md) and $t : \mathbb{N} \to \mathbb{N}$, let $G$ and $G'$ be simple graphs on the same finite set $V$ of $n$ nodes, $\mathrm{id}$ and $\mathrm{id}'$ [identifier assignments](id-assignment.md) for $V$ with the same exponent $c$, $x, x' : V \to I$ and $v \in V$. Suppose that $\mathrm{id}(u) = \mathrm{id}'(u)$ and $x(u) = x'(u)$ for every node $u$ at distance at most $t(n)$ from $v$ in $G$, and that every node at distance less than $t(n)$ from $v$ in $G$ has the same neighbours in $G$ as in $G'$. Then $A$, [run as a $t$-round algorithm](the-local-model.md), outputs the same at $v$ on $G$ with $\mathrm{id}$ and $x$ as on $G'$ with $\mathrm{id}'$ and $x'$.

This is [locality in the LOCAL model](state-after-congr-ball.md) with $k = t(n)$.

## Sources

- N. Linial, "Locality in distributed graph algorithms", *SIAM Journal on Computing* 21(1):193–201, 1992: §2.
