# Maximum subarray sum of a concatenation

Let $\alpha$ be an additive monoid with a linear
order such that $b \le c$ implies $a + b \le a + c$ and $b + a \le c + a$, and let $L$ and $R$ be
lists over $\alpha$. Suppose that $l$ is the maximum sum of a nonempty contiguous run of $L$, $r$
is the maximum sum of a nonempty contiguous run of $R$, $s$ is the maximum sum of a nonempty
suffix of $L$, and $p$ is the maximum sum of a nonempty prefix of $R$. Then
$\max(\max(l, r), s + p)$ is the maximum sum of a nonempty contiguous run of the concatenation of
$L$ followed by $R$.
