# Linear recurrences via powers of the companion matrix

Let $r$ be a natural number, let
$d_0, \dots, d_r$ be integers, and let $S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = 1$ and
$S(m + 1) = d_0 S(m) + d_1 S(m - 1) + \dots + d_r S(m - r)$ for every $m \ge r$. Let $\gamma(1)$
be the $(r + 1) \times (r + 1)$ integer matrix with rows and columns indexed by $0, \dots, r$
whose row $i < r$ has a $1$ in column $i + 1$ and zeros elsewhere, and whose last row is
$(d_r, d_{r-1}, \dots, d_0)$. With $v = (1, 0, \dots, 0)$ and $w = (S(0), \dots, S(r))^{T}$,
we have $S(n) = v \, \gamma(1)^n \, w$ for every natural number $n$.

The values $S(1), \dots, S(r)$ are arbitrary.

## Sources

- Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Lemma 1.
