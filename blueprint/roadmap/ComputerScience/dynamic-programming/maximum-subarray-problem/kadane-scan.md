# Kadane's scan

Given accumulators $e, b$ in an additive monoid $\alpha$ with a linear
order, the scan over the empty list returns $b$ at cost $0$. Over a list with first element $x$
and remaining elements $L$, it sets $e' = \max(x, e + x)$ and returns the result of the scan of
$L$ from the accumulators $e'$ and $\max(b, e')$, at cost $3$ plus the cost of that scan.

Here $e$ is the best sum of a nonempty run ending at the last element read and $b$ is the best
sum of any nonempty run read so far.
