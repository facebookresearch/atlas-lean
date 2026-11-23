# Correctness of divide-and-conquer maximum subarray

Let $\alpha$ be an additive monoid
with a linear order such that $b \le c$ implies $a + b \le a + c$ and $b + a \le c + a$. For every
list $xs$ over $\alpha$ and every $m \in \alpha$, the divide-and-conquer algorithm returns $m$ on
$xs$ if and only if $m$ is the maximum sum of a nonempty contiguous run of $xs$.
