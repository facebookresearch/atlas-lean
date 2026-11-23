# The pricing method weighs at most twice any cover of the listed edges

Let $w$ be
rational weights on a finite vertex set with $w(v) \ge 0$ for every vertex $v$, let $L$ be a
list of edges (ordered pairs of vertices), and let $C$ be a set of vertices such that every
pair $(u, v)$ in $L$ has $u \in C$ or $v \in C$. Then the total weight of the set returned by
the pricing method on $w$ and $L$ is at most $2 \sum_{v \in C} w(v)$.
