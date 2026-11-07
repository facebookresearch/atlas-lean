# Increasing-sequence and odd-divisor formulas for $C_n(q)/q^n$

Let $n \ge 1$, let
$\bar P_n$ be the Kassel–Reutenauer polynomial, and write $C_n(q)/q^n$ for the Laurent polynomial
$(q - 2 + q^{-1})\,\bar P_n(q + q^{-1})$ in $\mathbb{Z}[q, q^{-1}]$. For integers $h \ge 1$ and
$a$ let $IS(a, h) = \{a + 1, \dots, a + h\}$.

(i) We have

$$\frac{C_n(q)}{q^n} = \sum_{(h, a)} (-1)^h \left(q^a + q^{-a}\right),$$

where the sum runs over the pairs of integers $(h, a)$ with $1 \le h \le 2n$ and $-n \le a \le n$
such that the elements of $IS(a, h)$ sum to $n$. Moreover, if $h, h' \ge 1$ and $a, a'$ are
integers such that the elements of $IS(a, h)$ and those of $IS(a', h')$ both sum to $n$, and
$|a| = |a'|$, then $h = h'$ and $a = a'$.

(ii) For an odd divisor $d$ of $n$ put $u_d = n/d - (d - 1)/2$ and $v_d = n/d - (d + 1)/2$. Then

$$\frac{C_n(q)}{q^n} = \sum_{d \mid n,\ d \text{ odd}} (q^{u_d} + q^{-u_d} - q^{v_d} - q^{-v_d}),$$

and in the list of the exponents $u_d, -u_d, v_d, -v_d$ over all odd divisors $d$ of $n$, the
nonzero entries are pairwise distinct.

Every pair $(h, a)$ with $h \ge 1$ such that the elements of $IS(a, h)$ sum to $n$ satisfies
$h \le 2n$ and $|a| \le n$, so the sum in (i) runs over all such sequences.

## Sources

- C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4, Theorem 5.3 (`jis-2026-26.4.4-thm-23`).
