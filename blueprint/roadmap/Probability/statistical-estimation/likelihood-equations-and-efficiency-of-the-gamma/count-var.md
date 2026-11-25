# Biased sample variance of the counts

Let $\iota$ be a finite set of $n$ observations, with counts $k_i \in \mathbb{N}$ and size factors
$s_i$. The biased sample variance of the counts, with divisor $n$, is

$$V = \frac{1}{n} \sum_{i \in \iota} k_i^2 - M^2,$$

where $M$ is the [sample mean](count-mean.md). With the convention $x / 0 = 0$ it is $0$ when
$n = 0$.
