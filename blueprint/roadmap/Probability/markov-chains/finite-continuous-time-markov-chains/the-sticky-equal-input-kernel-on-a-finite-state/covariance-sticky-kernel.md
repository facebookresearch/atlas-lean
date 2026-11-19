# Covariance under the sticky kernel

Let $S$ be a finite set, $\pi, f, g : S \to \mathbb{R}$, $c \in \mathbb{R}$ and $K = K_\pi(c)$ the
[sticky kernel](sticky-kernel.md). Then

$$\sum_{i, j} \pi(i) K(i, j)\, f(i) g(j) - \Bigl(\sum_i \pi(i) f(i)\Bigr)\Bigl(\sum_j \pi(j) g(j)\Bigr) = c \Bigl( \sum_i \pi(i) f(i) g(i) - \Bigl(\sum_i \pi(i) f(i)\Bigr)\Bigl(\sum_j \pi(j) g(j)\Bigr) \Bigr) .$$

When $\pi$ is a probability vector and $0 \le c \le 1$, so that $P(X = i, Y = j) = \pi(i) K(i, j)$ is
the law of a stationary start followed by one step of the kernel, this reads
$\operatorname{Cov}(f(X), g(Y)) = c \operatorname{Cov}_\pi(f, g)$.
