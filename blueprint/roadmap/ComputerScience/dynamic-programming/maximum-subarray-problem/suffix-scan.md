# Right-to-left suffix scan

Let $\alpha$ be an additive monoid carrying a linear order.
For a nonempty list $x_1, \dots, x_n$ in $\alpha$, this timed computation returns the pair
$(x_1 + \dots + x_n, s)$, where $s$ is the maximum of the suffix sums $x_i + \dots + x_n$ over
$1 \le i \le n$. It scans from the right: the step for $x_i$ forms $x_i + (x_{i+1} + \dots + x_n)$
and takes its maximum with the best suffix sum found so far, at a cost of $2$ time units per
element, $2n$ in total. On the empty list it returns $(0, 0)$ at no cost.
