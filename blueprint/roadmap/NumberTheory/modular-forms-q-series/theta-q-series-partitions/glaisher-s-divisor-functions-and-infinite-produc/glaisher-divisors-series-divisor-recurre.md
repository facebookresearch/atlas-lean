# Glaisher's divisor functions as series-divisors

Let $n$ be a natural number. For a
positive integer $m$, write $\sigma(m)$ for the sum of the divisors of $m$, $d_B(m)$ and
$d_C(m)$ for the sums of the odd and of the even divisors of $m$, $d_D(m)$ and $d_E(m)$ for the
sums of the divisors $d$ of $m$ with $m/d$ odd and with $m/d$ even,
$d_F(m) = \sum_{d \mid m} (-1)^{d-1} d$ and $d_G(m) = \sum_{d \mid m} (-1)^{m/d-1} d$, and set all
of these to $0$ at $m = 0$. Let $p(m)$, $p_o(m)$, $p_e(m)$ and $p_d(m)$ be the numbers of
partitions of $m$, of partitions of $m$ into odd parts, into even parts and into distinct parts,
let $\bar p(m)$ be the number of overpartitions of $m$, let $r(m)$ be the number of integers $k$
with $k^2 = m$, and let $t(m)$ be the number of natural numbers $k$ with $k(k+1)/2 = m$. Then
$d_C(n) = 2 d_E(n)$, and, with every sum running over $1 \le i \le n$,
$n\,p(n) = \sum_i \sigma(i)\,p(n-i)$, $n\,p_o(n) = \sum_i d_B(i)\,p_o(n-i)$,
$n\,p_e(n) = \sum_i d_C(i)\,p_e(n-i)$, $n\,\bar p(n) = \sum_i 2 d_D(i)\,\bar p(n-i)$,
$n\,r(n) = \sum_i (-1)^{i+1} 2 d_D(i)\,r(n-i)$, $n\,t(n) = \sum_i d_F(i)\,t(n-i)$ and
$n\,p_d(n) = \sum_i d_G(i)\,p_d(n-i)$.

In the language of the source, these recurrences say that $\sigma$, $d_B$, $d_C$, $2 d_D$,
$i \mapsto (-1)^{i+1} 2 d_D(i)$, $d_F$ and $d_G$ are the series-divisors of the generating
functions of $p$, $p_o$, $p_e$, $\bar p$, $\varphi(q) = \sum_{k \in \mathbb{Z}} q^{k^2}$,
$\psi(q) = \sum_{k \ge 0} q^{k(k+1)/2}$ and $p_d$ respectively.

## Sources

- Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 9 (`jis-2024-24.1.6-thm-9`).
