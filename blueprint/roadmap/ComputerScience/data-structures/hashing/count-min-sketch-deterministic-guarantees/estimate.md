# Estimate

Let $X$ be a finite universe of items with natural-number frequencies $f \colon X \to \mathbb{N}$, and let $H_0, \dots, H_{d-1}$ be $d > 0$ hash functions $X \to \mathbb{N}$. The Count-Min estimate of $x$ is the minimum, over $j < d$, of the counter of the bucket $H_j(x)$ under $H_j$.
