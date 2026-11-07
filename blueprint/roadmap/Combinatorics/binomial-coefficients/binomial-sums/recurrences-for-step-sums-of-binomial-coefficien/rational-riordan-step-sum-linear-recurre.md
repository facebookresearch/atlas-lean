# Step sums of a rational Riordan array satisfy a common recurrence

Let
$g_1, g_2, h_1, h_2 \in \mathbb{Z}[x]$ with $g_2(0) = h_1(0) = h_2(0) = 1$, let $\nu \ge 1$ and
$k \ge 1$ be natural numbers, and in $\mathbb{Q}[[x]]$ let $g = g_1/g_2$ and
$h = x^\nu h_1/h_2$. For $p, n \in \mathbb{N}$ let
$a_p(n) = \sum_{j=0}^{n} [x^n]\, g h^{kj+p}$. Then there are $r \in \mathbb{N}$ and integers
$\alpha_1, \ldots, \alpha_r$ such that $a_p(n) = \sum_{i=1}^{r} \alpha_i a_p(n - i)$ for every
$p < k$ and every $n \ge r$.

Since $h$ has no constant term, $[x^n]\, g h^m = 0$ for $m > n$, so $a_p(n)$ is the full sum
over all $j \ge 0$.

## Sources

- Eduardo H. M. Brietzke, *Recurrence Relations for Sums of Binomial Coefficients and Some Generalizations*, Journal of Integer Sequences 27 (2024), Article 24.3.4, Proposition 11.
