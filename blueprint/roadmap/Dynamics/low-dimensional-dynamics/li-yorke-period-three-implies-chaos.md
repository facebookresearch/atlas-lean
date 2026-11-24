# Li–Yorke: period three implies chaos

Let $J$ be an interval and $F : J \to J$ continuous, and suppose some $a \in J$ has $b = F(a)$, $c = F^2(a)$, $d = F^3(a)$ with $d \le a < b < c$ or $d \ge a > b > c$; a point of period $3$ satisfies this. Li and Yorke (1975, Theorem 1) prove: (T1) for every $k \ge 1$ there is a periodic point in $J$ of period $k$; (T2) there is an uncountable set $S \subset J$ containing no periodic points such that (A) $\limsup_n |F^n(p) - F^n(q)| > 0$ and $\liminf_n |F^n(p) - F^n(q)| = 0$ for all $p \ne q$ in $S$, and (B) $\limsup_n |F^n(p) - F^n(q)| > 0$ for every $p \in S$ and every periodic point $q$. The [Li–Yorke theorem on periods](../../Dynamics/low-dimensional-dynamics/li-yorke-period-three-implies-periods.md) is the special case of (T1) in which $J = [0, 1]$ and $F$ has a point of minimal period $3$. Li and Yorke note that the population map $F(x) = rx(1 - x/K)$ on $[0, K]$ satisfies the hypothesis for $r \in (3.84, 4]$.

## Depends on

- [Li–Yorke theorem: period three implies all periods](../../Dynamics/low-dimensional-dynamics/li-yorke-period-three-implies-periods.md)

## Expansion

1. The hypothesis on the first three iterates and why a period-three point satisfies it.
2. (T1) under the weaker hypothesis on $J$.
3. (T2): the construction of the scrambled set $S$ from nested intervals.
4. Application to the logistic map for $r \in (3.84, 4]$ and to its truncation $\max\{0, rx(1 - x/K)\}$ for $r > 4$, as in the source.

## Sources

- T.-Y. Li and J. A. Yorke, Period three implies chaos, Amer. Math. Monthly 82 (1975), 985–992, Theorem 1 and the remarks after it. <https://doi.org/10.1080/00029890.1975.11994008>
- S. Ruette, *Chaos on the Interval*, University Lecture Series 67, American Mathematical Society, 2017, Chapter 5.
