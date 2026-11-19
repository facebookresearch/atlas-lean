# Three-series necessity, second half of the variance step

Let $\mu$ be a probability measure, let $Y_0, Y_1, \dots$ be independent measurable real random
variables and let $A > 0$ with $|Y_n| \le A$ everywhere for every $n$. If the partial sums
$\sum_{i < n} Y_i$ converge almost surely, then $\sum_n \operatorname{Var}(Y_n) < \infty$. The
proof is by symmetrization: the symmetrized sums are centered, so the Paley–Zygmund inequality
gives a uniform lower bound on block-tail probabilities, which contradicts convergence in measure
unless the variances are summable.
