# An index lies in the block it is assigned to

Let $M : \mathbb{N} \to \mathbb{N}$ satisfy
$M(0) = 0$, and suppose every $i \in \mathbb{N}$ satisfies $i < M(j + 1)$ for some $j$. For
every $i \in \mathbb{N}$, if $k$ is the block index of $i$ (the least $k$ with
$i < M(k + 1)$), then $M(k) \le i < M(k + 1)$.
