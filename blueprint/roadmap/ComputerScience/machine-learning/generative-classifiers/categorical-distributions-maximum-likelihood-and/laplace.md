# Laplace smoothing of categorical counts

Let $\alpha$ be a finite nonempty set of categories and $n : \alpha \to \mathbb{N}$ the observed counts. Laplace (add-one) smoothing estimates the probability of category $a$ by $(n(a) + 1) / (N + K)$, where $N = \sum_b n(b)$ and $K = |\alpha|$ is the number of categories.
