# Expected running time

Let $A$ be an algorithm on inputs of a type $\gamma$ whose running
time $T_A(x)$ on each input $x$ is a natural number, and let $D$ be a probability mass function on
$\gamma$. The expected running time of $A$ under $D$ is the extended nonnegative expectation
$\sum_{x \in \gamma} D(x)\, T_A(x) \in [0, \infty]$ of the running time, the sum taken over all
inputs.

Valuing the expectation in $[0, \infty]$ records a divergent expected time as $\infty$; a
real-valued integral would collapse it to $0$.
