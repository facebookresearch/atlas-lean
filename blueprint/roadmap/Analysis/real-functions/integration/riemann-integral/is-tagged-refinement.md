# Tagged-refinement data

Let $T$ and $T'$ be tagged partitions of $[a, b]$ with points
$a = x_0 < \dots < x_n = b$ and $a = x'_0 < \dots < x'_{n'} = b$ respectively. Tagged-refinement
data from $T$ to $T'$ consist of a map $\sigma$ assigning to each index $j < n'$ an index
$\sigma(j) < n$ such that $x_{\sigma(j)} \le x'_j$ and $x'_{j+1} \le x_{\sigma(j)+1}$ for every
$j < n'$ (so the $j$-th subinterval of $T'$ lies in the $\sigma(j)$-th subinterval of $T$), and
such that for every $k < n$ the lengths assigned to $k$ add up to its length:
$\sum_{j < n',\ \sigma(j) = k} (x'_{j+1} - x'_j) = x_{k+1} - x_k$. The tags of $T$ and $T'$
play no role.

Such data exist whenever every point of $T$ is a point of $T'$.
