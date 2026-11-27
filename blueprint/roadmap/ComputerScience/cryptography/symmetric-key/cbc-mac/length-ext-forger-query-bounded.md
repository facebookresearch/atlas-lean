# Length Ext Forger query Bounded

Let $X$ be an additive commutative group and $x \in X$. The [length-extension forger](length-ext-forger.md) for $x$ is query-bounded by $1$: for every value of its coins, every execution path makes **at most** one tagging query.

The theorem proves this upper bound only. As an observation about the definition (not the conclusion of the theorem), the forger in fact always makes exactly one query, on the one-block message $[x]$.
