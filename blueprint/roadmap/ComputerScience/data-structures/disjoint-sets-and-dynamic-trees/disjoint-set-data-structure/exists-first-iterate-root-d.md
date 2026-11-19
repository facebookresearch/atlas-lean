# The root is reached in fewer parent steps than there are nodes

Let $S$ be a
union-find structure with $n$ nodes and parent map $p$, and let $x < n$. Then there is $d < n$
such that $p^d(x)$ is the root of $x$ and $p^k(x)$ is not the root of $x$ for every $k < d$.
