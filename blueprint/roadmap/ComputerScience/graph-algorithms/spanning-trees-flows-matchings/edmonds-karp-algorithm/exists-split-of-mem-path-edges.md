# A step of a chain splits it into two walks

Let $r$ be a relation and $p$ an $r$-chain (a nonempty list whose consecutive entries are related by $r$) from $s$ to $t$. If $(a, b)$ is a pair of consecutive entries of $p$, then $r(a, b)$ holds and there are $r$-walks from $s$ to $a$ of length $i$ and from $b$ to $t$ of length $j$ with $|p| = i + j + 2$.

This is the bookkeeping behind the distance arguments of Edmonds and Karp: an arc of a shortest augmenting path sits at a definite position, with a prefix walk before it and a suffix walk after it.
