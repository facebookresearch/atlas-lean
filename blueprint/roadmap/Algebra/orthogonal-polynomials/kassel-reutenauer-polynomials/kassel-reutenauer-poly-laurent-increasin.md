# Increasing-sequence formula for the Kassel–Reutenauer polynomials

Let $n \ge 1$ and
work in the ring $\mathbb{Z}[q, q^{-1}]$ of Laurent polynomials. For integers $a$ and $h$ let
$IS(a, h) = \{a+1, \dots, a+h\}$. For an odd divisor $d$ of $n$ put $r_n(d) = n/d - (d+1)/2$,
$A_d = IS(r_n(d), d)$ and $\check A_d = IS(-r_n(d) - 1, 2n/d)$. Then the Kassel–Reutenauer
polynomial $\bar P_n$ satisfies

$$
\bar P_n(q + q^{-1}) = \sum_{d \mid n,\ d \text{ odd},\ r_n(d) \ge 0}\
\sum_{i \in \check A_d \setminus A_d} q^i -
\sum_{d \mid n,\ d \text{ odd},\ r_n(d) < 0}\ \sum_{i \in A_d \setminus \check A_d} q^i.
$$

The left-hand side is the paper's $P_n(q)/q^{n-1}$.

## Sources

- C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 6.2 (`jis-2026-26.4.4-prop-27`).
