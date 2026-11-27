# Running time of divide-and-conquer maximum subarray

Let $\alpha$ be an additive monoid
with a linear order. On a nonempty list over $\alpha$ of length $n$, the cost $T$ of the
divide-and-conquer maximum subarray algorithm satisfies
$T + 3 \le 2n\lceil \log_2 n \rceil + 3n$, that is, $T \le 2n\lceil \log_2 n \rceil + 3(n - 1)$.
