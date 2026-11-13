# Zeta function of the Hilbert scheme of points on the two-dimensional torus

Let $p$ be a
prime, $k \ge 1$, $q = p^k$ and $n \ge 1$. For $m \ge 1$ let $\mathbb{F}_{q^m}$ be the field with
$q^m$ elements and let $N_m$ be the number of ideals $I$ of the Laurent polynomial ring
$\mathbb{F}_{q^m}[x^{\pm 1}, y^{\pm 1}]$ (the group algebra of $\mathbb{Z} \times \mathbb{Z}$)
such that the quotient by $I$ has dimension $n$ over $\mathbb{F}_{q^m}$; this is the number of
$\mathbb{F}_{q^m}$-points of the Hilbert scheme $H^n$ of $n$ points on the torus. For an odd
divisor $d$ of $n$ put $r_n(d) = n/d - (d + 1)/2$, $a_d = n + r_n(d)$ and $b_d = n - r_n(d)$.
Then the zeta function $Z(t) = \exp\big(\sum_{m \ge 1} N_m t^m / m\big)$, a formal power series
with rational coefficients, is

$$Z(t) = \prod_{d} \frac{(1-q^{a_d}t)(1-q^{b_d}t)}{(1-q^{a_d+1}t)(1-q^{b_d-1}t)},$$

the product running over the odd divisors $d$ of $n$.

The exponents $a_d$, $b_d$, $a_d + 1$ and $b_d - 1$ are nonnegative integers.

## Sources

- C. Kassel and C. Reutenauer, *Pairs of Intertwined Integer Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.4, Proposition 5.5 (`jis-2026-26.4.4-prop-25`).
