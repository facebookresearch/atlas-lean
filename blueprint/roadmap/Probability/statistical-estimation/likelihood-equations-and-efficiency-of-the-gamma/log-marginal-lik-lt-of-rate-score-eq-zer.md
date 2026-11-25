# At a fixed shape the rate root is the global maximizer over b > 0

Let $\iota$ be a finite nonempty set of $n \ge 1$ observations, with counts $k_i \in \mathbb{N}$ and
size factors $s_i$. Let $a > 0$, let the size factors be positive, and let $\hat b > 0$ solve the
[rate score](rate-score.md) equation $S_b(a, \hat b) = 0$. Then $\ell(a, b) < \ell(a, \hat b)$ for
every $b > 0$ with $b \ne \hat b$, where $\ell$ is the
[log marginal likelihood](log-marginal-lik.md): $\hat b$ is the unique maximizer of
$b \mapsto \ell(a, b)$ over $b > 0$.
