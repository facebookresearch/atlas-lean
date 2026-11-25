# With a positive count a rate root exists at every shape

Let $\iota$ be a finite nonempty set of $n \ge 1$ observations, with counts $k_i \in \mathbb{N}$ and
size factors $s_i$. If some count $k_i$ is positive, then for every shape $a > 0$ and positive size
factors $s_i > 0$ the [rate score](rate-score.md) equation has a positive solution: $S_b(a, b) = 0$
for some $b > 0$. It is the [only positive solution](rate-score-eq-zero-unique.md), and it is the
[unique maximizer](log-marginal-lik-lt-of-rate-score-eq-zer.md) over $b > 0$ of
$b \mapsto \ell(a, b)$, with $\ell$ the [log marginal likelihood](log-marginal-lik.md).
