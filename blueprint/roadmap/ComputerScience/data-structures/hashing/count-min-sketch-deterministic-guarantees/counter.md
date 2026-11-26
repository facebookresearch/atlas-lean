# Counter

Let $X$ be a finite universe of items with natural-number frequencies $f \colon X \to \mathbb{N}$ and $h \colon X \to \mathbb{N}$ a hash function. The counter of bucket $b$ is the total frequency $\sum_{y \in X,\, h(y) = b} f(y)$ of the items hashed to $b$.
