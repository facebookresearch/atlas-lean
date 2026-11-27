# Counter le freq add collision

Let $X$ be a finite universe of items with natural-number frequencies $f \colon X \to \mathbb{N}$ and $h \colon X \to \mathbb{N}$ a hash function. The counter of the bucket $h(x)$ is at most $f(x)$ plus the total frequency of the other items $y \ne x$ with $h(y) = h(x)$.
