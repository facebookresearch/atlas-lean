# Limit of the fixed-hook generating functions

Let $m \ge 2$ be a natural number and work
in $\mathbb{Q}[[q]]$. For $j \in \mathbb{N}$ write $(q;q)_j = \prod_{i=1}^{j} (1 - q^i)$ and
$(q^m;q)_j = \prod_{i=0}^{j-1} (1 - q^{m+i})$. Then for every natural number $n$ there is a $K$
such that for every $k \ge K$ the coefficient of $q^n$ in

$$
\frac{q^{m-1}}{\prod_{i=0}^{n} (1 - q^{k+i})}
\sum_{l=1}^{k} \frac{q^{(m-1)(k-l)} (q^m;q)_{l-1}}{(q;q)_{l-1} (q;q)_{k-l}}
$$

equals the coefficient of $q^n$ in

$$
\frac{q^{m-1}}{(1 - q^{m-1}) (q;q)_{n+1}}.
$$

This is the coefficientwise ($q$-adic) form of the limit

$$
\lim_{k \to \infty} \frac{q^{m-1}}{(q^k;q)_\infty}
\sum_{l=1}^{k} \frac{q^{(m-1)(k-l)} (q^m;q)_{l-1}}{(q;q)_{l-1} (q;q)_{k-l}}
= \frac{q^{m-1}}{(1 - q^{m-1}) (q;q)_\infty},
$$

where $(a;q)_\infty = \prod_{i \ge 0} (1 - a q^i)$: for the coefficient of $q^n$, the products
$(q^k;q)_\infty$ and $(q;q)_\infty$ are replaced by their first $n + 1$ factors, which changes no
coefficient below $q^{n+1}$.

## Sources

- Philip Cuthbertson, *Fixed Hooks in Arbitrary Columns of Partitions*, INTEGERS 25 (2025), Article A28, Theorem 5 (`integers-2025-A28-thm-5`).
