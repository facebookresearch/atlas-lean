# Expander Chernoff bound with gap-dependent exponent and constant 36

Let $G$ be a regular multigraph on a finite nonempty set $V$ with nonempty label set and spectral expansion $\lambda$, and let $B \subseteq V$ have density $\beta$. For a walk with $t$ steps from a uniform start, visiting $v_0, \dots, v_t$, and every $\delta > 0$,

$$\Pr\Bigl[\Bigl|\frac{|\{i \le t : v_i \in B\}|}{t + 1} - \beta\Bigr| > \delta\Bigr] \le 2\exp\Bigl(-\frac{(1 - \lambda)\,\delta^2\,(t + 1)}{36}\Bigr).$$

Unlike the additive form $\lambda + \varepsilon$, this deviation bound is useful for every $\lambda < 1$.

## Proof sketch

For $g$ of mean zero with $|g| \le 1$, the moment generating function $\mathbb{E}\exp(r\sum_i g(v_i))$ is the average of a weighted walk alternating $W$ with multiplication by $P = e^{rg}$. Track the mean $a$ and the root-mean-square $\|y\|$ of the mean-zero part: one step is dominated by a nonnegative $2\times 2$ matrix, and the potential $|a| + \theta\|y\|$ with $\theta = 4r/(1 - \lambda)$ grows by at most $1 + 9r^2/(1 - \lambda)$ when $4r \le 1 - \lambda$. Markov's inequality on each tail and a union bound give the claim.

## Depends on

- [Probability of an event for a random walk on a regular graph](../../graph-families-and-operations/expander-graphs/walk-prob.md)
- [Spectral expansion, second eigenvalue and edge expansion of a regular multigraph](../../graph-families-and-operations/expander-graph-operations/spectral-expansion-second-eigenvalue-and-edge-expansion.md)

## Proof depends on

- [Chernoff bound for expander walks](../../graph-families-and-operations/expander-graphs/chernoff-bound-expander-walk.md)

## Sources

- S. Arora, B. Barak, "Computational Complexity: A Modern Approach", web draft of 2007-01-08, 2007.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science, 2012.
