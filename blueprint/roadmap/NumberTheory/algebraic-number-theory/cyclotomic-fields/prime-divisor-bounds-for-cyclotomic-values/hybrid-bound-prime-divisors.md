# Hybrid bound for prime divisors of $x^n - 1$

Let $n = p_1^{a_1} \cdots p_m^{a_m}$ with distinct primes
$p_1, \dots, p_m$ (in any order) and exponents $a_i \ge 1$, let $x > 1$ be a natural number, and
let $\omega_n$ be the number of distinct prime factors of $x^n - 1$. For $0 \le j \le m$ let
$\Pi^j$ be the set of primes $\rho$ with $\rho \equiv 1 \pmod{p_j}$ (no condition when $j = 0$)
and $\rho \not\equiv 1 \pmod{p_s}$ for $j < s \le m$, and list its elements in increasing order as
$r_{0,j} < r_{1,j} < \cdots$. Then there are natural numbers $k_0, \dots, k_m$ with
$k_0 + \cdots + k_m = \omega_n$ such that each $\Pi^j$ has at least $k_j$ elements and, for every
$0 \le t \le m$,

$$1 + \prod_{j=0}^{t} \prod_{i < k_j} r_{i,j} \le x^{p_1^{a_1} \cdots p_t^{a_t}}.$$

The source states this as
$x \ge \min_{k_0 + \cdots + k_m = \omega_n} \max_{0 \le t \le m}
\bigl(1 + \prod_{j \le t} \prod_{i \le k_j} r_{i,j}\bigr)^{T(t)}$ with
$T(t) = \prod_{s=1}^{t} p_s^{-a_s}$ and primes indexed from $1$; raising each bound to the power
$p_1^{a_1} \cdots p_t^{a_t}$ gives the form above. The parts $k_j$ may be $0$: the source writes
$k_j \in \mathbb{Z}^+$, but with positive parts the claim fails for $n = 3$ and $x = 2$, where
$x^3 - 1 = 7$ and $\omega_n = 1$ has no composition into two positive parts.

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Theorem 1.
