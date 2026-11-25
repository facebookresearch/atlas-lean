# Marginal entropy

For a finite set $\alpha$, a natural number $n$, a real-valued function
$\mu$ on $\alpha^n$ and a set $S \subseteq \{0, \dots, n-1\}$ of coordinates, let $P_S$ be the
marginal of $\mu$ on $S$: for $y \in \alpha^S$, $P_S(y)$ is the sum of $\mu(x)$ over the
$x \in \alpha^n$ whose restriction to $S$ is $y$. The marginal entropy of $\mu$ on $S$ is
$H_S(\mu) = -\sum_{y \in \alpha^S} P_S(y) \log P_S(y)$, where $\log t$ is the natural logarithm
of $|t|$ for $t \neq 0$ and $\log 0 = 0$.
