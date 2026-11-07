# Run length transform of a linear recurrence (Rampersad–Wiebe Theorem 1)

Let $r \ge 0$, let
$d_0, \dots, d_r$ be integers, and let $S : \mathbb{N} \to \mathbb{Z}$ satisfy $S(0) = 1$ and
$S(m + 1) = d_0 S(m) + d_1 S(m - 1) + \dots + d_r S(m - r)$ for all $m \ge r$. Let $T$ be the run
length transform of $S$, let $v = (1, 0, \dots, 0)$ and $w = (S(0), \dots, S(r))^\top$, let
$\gamma(0)$ be the $(r + 1) \times (r + 1)$ matrix with first column $w$ and zeros elsewhere, and
let $\gamma(1)$ be the $(r + 1) \times (r + 1)$ companion matrix with ones on the superdiagonal,
last row $(d_r, \dots, d_0)$ and zeros elsewhere. Then for every natural number $n$ with binary
digits $b_1 b_2 \cdots b_t$, most significant first,
$T(n) = v \, \gamma(b_1) \gamma(b_2) \cdots \gamma(b_t) \, w$, where for $n = 0$ the product of
matrices is empty and equals the identity.

## Sources

- Narad Rampersad and Max Wiebe, *Sums of Products of Binomial Coefficients Mod 2 and 2-Regular Sequences*, INTEGERS 24 (2024), Article A73, Theorem 1.
