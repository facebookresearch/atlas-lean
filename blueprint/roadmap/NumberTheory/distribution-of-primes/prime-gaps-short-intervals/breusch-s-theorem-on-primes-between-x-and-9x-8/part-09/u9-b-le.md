# Contribution of primes with $p^2 > 2100n$

Write $v_p(m)$ for the exponent of $p$ in $m$
and $\mu$ for the Möbius function, and set
$\nu_p(n) = \sum_{d \mid 210} \mu(d)\bigl(v_p((2100n/d)!) - v_p((1890n/d)!) -
v_p((210n/d)!)\bigr)$. For every natural number $n \ge 1$, the sum of $\nu_p(n) \log p$ over the
primes $p \le 1890n$ with $p^2 > 2100n$ satisfies

$$
\sum_{\substack{p \le 1890n \text{ prime} \\ p^2 > 2100n}} \nu_p(n) \log p \le
\left(\frac{18900}{279} + \frac{18900}{657} + \frac{18900}{963}\right) n \log 3.4.
$$
