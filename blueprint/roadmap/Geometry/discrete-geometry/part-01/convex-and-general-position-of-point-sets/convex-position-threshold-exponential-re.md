# Erdős Problem 651 has a negative answer

For natural numbers $k$ and $n$ let $f_k(n)$ be the
least $m$ such that every set of $m$ points of $\mathbb{R}^k$ in general position (any at most
$k + 1$ of them affinely independent) contains $n$ points in convex position (none of them in the
convex hull of the others), with $f_k(n) = 0$ if there is no such $m$. It is not the case that for
every $k \ge 2$ there is a real $c > 0$ with $(1 + c)^n < f_k(n)$ for all sufficiently large $n$.

Pohoata and Zakharov proved $f_d(n) = 2^{o(n)}$ for every $d \ge 3$, so for $k = 3$ and every
$c > 0$ the bound $f_3(n) \le (1 + c)^n$ holds for all large $n$; erdosproblems.com/651 lists the
problem as disproved.

## Sources

- T. F. Bloom, Erdős Problems, Problem #651, https://www.erdosproblems.com/651 (status DISPROVED (LEAN)); resolution: C. Pohoata and D. Zakharov, Convex polytopes from fewer points, arXiv:2208.04878 (2022), abstract: ES_d(n) = 2^{o(n)} for all d ≥ 3, ES_d(n) being the least number such that any ES_d(n) points in general position in ℝ^d contain n points in convex position; erdosproblems.com/651: the answer is no, even for k = 3, https://arxiv.org/abs/2208.04878.
