# Li–Yorke: period three implies chaos

Let $J$ be an interval and $F : J \to J$ continuous, and suppose some $a \in J$ has $b = F(a)$, $c = F^2(a)$, $d = F^3(a)$ with $d \le a < b < c$ or $d \ge a > b > c$; every orbit of period $3$ contains such a point, after rotating the orbit if needed (its smallest point if the orbit visits its points in increasing order, its largest point otherwise), though an arbitrary point of the orbit need not satisfy it. Li and Yorke (1975, Theorem 1) prove: (T1) for every $k \ge 1$ there is a periodic point in $J$ of period $k$; (T2) there is an uncountable set $S \subset J$ containing no periodic points such that (A) $\limsup_n |F^n(p) - F^n(q)| > 0$ and $\liminf_n |F^n(p) - F^n(q)| = 0$ for all $p \ne q$ in $S$, and (B) $\limsup_n |F^n(p) - F^n(q)| > 0$ for every $p \in S$ and every periodic point $q$. The [Li–Yorke theorem on periods](../../Dynamics/low-dimensional-dynamics/li-yorke-period-three-implies-periods.md) is the special case of (T1) in which $J = [0, 1]$ and $F$ has a point of minimal period $3$. For $K > 0$ and $r \in (3.84, 4]$, the population map $F(x) = rx(1 - x/K)$ maps $J = [0, K]$ into itself and satisfies the hypothesis, as Li and Yorke note. For $r > 4$ the truncation $G(x) = \max(0, rx(1 - x/K))$ is not a self-map of $[0, K]$, since $G(K/2) = rK/4 > K$, but it is a continuous self-map of $J = [0, rK/4]$, on which $0 \le G \le rK/4$; the point $a \in (0, K/2)$ with $G(a) = K/2$ has $G^2(a) = rK/4$ and $G^3(a) = 0$, so $d = 0 < a < b = K/2 < c = rK/4$.

## Expansion

1. The hypothesis on the first three iterates and why every orbit of period three contains a point satisfying it, after rotating the orbit if needed.
2. (T1) under the weaker hypothesis on $J$.
3. (T2): the construction of the scrambled set $S$ from nested intervals.
4. Application to the logistic map on $[0, K]$ for $r \in (3.84, 4]$, and to its truncation $\max\{0, rx(1 - x/K)\}$ on $[0, rK/4]$ for $r > 4$; the source states the truncated example on $[0, K]$, where it is not a self-map.

## Sources

- T.-Y. Li and J. A. Yorke, Period three implies chaos, Amer. Math. Monthly 82 (1975), 985–992, Theorem 1 and the remarks after it. <https://doi.org/10.1080/00029890.1975.11994008>
- S. Ruette, *Chaos on the Interval*, University Lecture Series 67, American Mathematical Society, 2017, Chapter 5.
