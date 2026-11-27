# Shortest walks to $\pm(a - 1)$ in $G(-2n + 1, -2n + a)$

Let $m \ge 1$ be an integer and
$a = 1 + 3^m$ or $a = 1 - 3^m$. Then in $G(-2n + 1, -2n + a)$ the least $k \in \mathbb{N}$ such
that $a - 1$ is a $k$-descendant of $0$ (the end of a directed walk of exactly $k$ edges from
$0$) is $3^m$, and the least $k$ such that $-(a - 1)$ is a $k$-descendant of $0$ is also $3^m$.

The paper states this for every $a \notin \{0, 2\}$, which is false: for $a = 6$ the shortest
walk from $0$ to $5$ has $4$ edges. Its proof uses that the cycle through $0$ has $|a - 1|$
edges, which holds when the digraph has a single component.

## Sources

- Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 16.
