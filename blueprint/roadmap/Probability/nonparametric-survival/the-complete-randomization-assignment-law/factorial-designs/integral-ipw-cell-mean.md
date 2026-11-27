# Unbiasedness of inverse-probability-weighted cell means

Let $U$ be a finite population of $N \ge 1$ units and let $\pi_{ic} > 0$ be cell probabilities with $\sum_c \pi_{ic} = 1$ for every unit $i$. Assign units independently, unit $i$ to cell $c$ with probability $\pi_{ic}$. Then for every $y : U \to \mathbb{R}$ and every cell $c$

$$\mathbb{E}\Big[\sum_{i : f(i) = c} \frac{y_i}{N \pi_{ic}}\Big] = \frac1N \sum_{i \in U} y_i.$$

Realized cells may be empty; no nonempty-cell condition is needed.

## Sources

- T. Dasgupta, N. S. Pillai and D. B. Rubin, "Causal inference from $2^K$ factorial designs using the potential outcomes model", arXiv:1211.2481, Section 3.1, equations (1) and (2).
- D. G. Horvitz and D. J. Thompson, "A generalization of sampling without replacement from a finite universe", *Journal of the American Statistical Association* 47 (1952), 663–685.
