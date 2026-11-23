# Block index for a cutoff sequence

Let $M : \mathbb{N} \to \mathbb{N}$ be such that
every $i \in \mathbb{N}$ satisfies $i < M(k + 1)$ for some $k$. The block index of
$i \in \mathbb{N}$ is the least $k$ with $i < M(k + 1)$.

When $M$ is monotone and $M(0) = 0$, the block index of $i$ is the unique $k$ with
$M(k) \le i < M(k + 1)$.
