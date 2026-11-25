# Invariant of Kadane's scan

Let $\alpha$ be an additive monoid with a linear order such
that $a \le b$ implies $a + c \le b + c$. Let $p$ be a list over $\alpha$, let $e$ be the maximum
sum of a nonempty suffix of $p$, and let $b$ be the maximum sum of a nonempty contiguous sublist
of $p$. Then for every list $r$ over $\alpha$, the value that Kadane's scan from the accumulators
$e$ and $b$ returns on $r$ is the maximum sum of a nonempty contiguous sublist of the list $p$
followed by $r$.
