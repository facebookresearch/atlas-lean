# What the scan holds after each round

Let $x_0, x_1, \dots$ be a sequence in a monoid
$M$, let $k$ and $i$ be natural numbers, and let $m = \min(i + 1, 2^k)$. After $k$ rounds of the
Kogge–Stone scan, position $i$ holds the product $x_{i+1-m} \cdots x_i$ of the $m$ consecutive
inputs ending at $i$, taken in increasing order of index.
