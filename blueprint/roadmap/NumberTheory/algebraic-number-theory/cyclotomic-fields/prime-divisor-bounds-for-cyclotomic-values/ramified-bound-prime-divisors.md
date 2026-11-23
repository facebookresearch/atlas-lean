# Ramified bound on the number of prime divisors of $x^n - 1$

Let $n = p_1^{a_1} \cdots p_m^{a_m}$ with primes
$p_1 < \cdots < p_m$ (the ordering the source fixes at the start of its Section 5) and exponents
$a_i \ge 1$, let $x > 1$ be a natural number, and let $\omega_n$ be the number of distinct prime
factors of $x^n - 1$. For $0 \le j \le m$ let $\Pi^j$ be the set of primes $\rho$ with
$\rho \equiv 1 \pmod{p_j}$ (no condition when $j = 0$) and $\rho \not\equiv 1 \pmod{p_s}$ for
$j < s \le m$, list its elements in increasing order as $r_{0,j} < r_{1,j} < \cdots$, and put
$R_j(k) = \prod_{i < k} r_{i,j}$. Fix $1 \le \alpha \le m$, and let $\tau \le m$ and $b$ be such
that $p_\alpha = r_{b,\tau}$. Then there are natural numbers $k_0, \dots, k_m$ with
$k_0 + \cdots + k_m = \omega_n$ such that each $\Pi^j$ has at least $k_j$ elements, and:

- if $p_\alpha \mid x^n - 1$, then $k_\tau > 0$ and, for every $0 \le t \le m$,
  $1 + \prod_{j=0}^{t} B_j \le x^{p_1^{a_1} \cdots p_t^{a_t}}$, where
  $B_\tau = p_\alpha R_\tau(k_\tau - 1)$ if $k_\tau \le b$ and $B_\tau = R_\tau(k_\tau)$ if
  $k_\tau > b$, $B_\alpha = p_\alpha^{a_\alpha} R_\alpha(k_\alpha)$, and $B_j = R_j(k_j)$ for
  every other $j$;
- if $p_\alpha \nmid x^n - 1$, then $\Pi^\tau$ has more than $k_\tau$ elements and, for every
  $0 \le t \le m$, $1 + \prod_{j=0}^{t} B'_j \le x^{p_1^{a_1} \cdots p_t^{a_t}}$, where
  $B'_\tau = \prod_{i \le k_\tau,\, i \ne b} r_{i,\tau}$ if $k_\tau > b$, and $B'_j = R_j(k_j)$
  otherwise.

So in the divisible case block $\tau$ with $k_\tau \le b$ has its largest factor
$r_{k_\tau - 1,\tau}$ replaced by $p_\alpha$ and block $\alpha$ gains the factor
$p_\alpha^{a_\alpha}$; otherwise block $\tau$ with $k_\tau > b$ drops $p_\alpha$ and takes the
next element of $\Pi^\tau$ instead. The source states the bound as
$x \ge \min_{k_0 + \cdots + k_m = \omega_n} \max_t
\bigl(1 + \prod_{j \le t} \delta_\alpha(j) \prod_{i \le k_j} r_{i,j}\bigr)^{T(t)}$ with
$T(t) = \prod_{s=1}^{t} p_s^{-a_s}$ and primes indexed from $1$ (so its condition $k_\tau < b$ is
$k_\tau \le b$ here); raising each bound to the power $p_1^{a_1} \cdots p_t^{a_t}$ gives the form
above, with parts $k_j \ge 0$ as in the hybrid bound. In the divisible case $k_\tau > 0$ is
required because the source's $\delta_\alpha(\tau)$ is undefined at $k_\tau = 0$. The source's
worked example ($n = 3$ and $\omega_3 = 10$: $x \ge 4387$ if $3 \mid x^3 - 1$, and $x \ge 5423$
otherwise) is reproduced by this reading. Definitions follow the arXiv version
(arXiv:2412.00010), whose statement matches the journal record.

## Sources

- Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026), Article A95, Theorem 2.
