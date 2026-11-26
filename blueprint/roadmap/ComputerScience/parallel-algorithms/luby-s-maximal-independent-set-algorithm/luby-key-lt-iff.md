# Comparing keys in Luby's algorithm

For priorities $p : \{0, \dots, n-1\} \to \mathbb{N}$ and vertices $u, v$, the key of $v$ is smaller than the key of $u$ if and only if $p(v) < p(u)$, or $p(v) = p(u)$ and $v < u$. So keys order vertices lexicographically by priority and then by index.
