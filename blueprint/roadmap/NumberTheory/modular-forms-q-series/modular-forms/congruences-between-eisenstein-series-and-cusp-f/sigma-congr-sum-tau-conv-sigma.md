# Lu's congruence for the divisor sums $\sigma_{k-1}(n)$

Let $k \ge 12$ be even with
$k \ne 14$. For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise;
for $w \ge 1$ let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$ and $\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$, and
for $i, n \in \mathbb{N}$ let $c_i(n)$ be the coefficient of $q^n$ in $\Delta^i G_{k-12i}$, that
is, the additive convolution $(\tau^{*i} * \sigma_{k-12i-1})(n)$, where $\tau(n)$ is the
coefficient of $q^n$ in $\Delta$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the absolute value of
the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest divisor of $N_k$
that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For rationals $x, y$
and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has denominator coprime
to $N$. Let $m = \lfloor k/12 \rfloor - 1$ if $k \equiv 2 \pmod{12}$ and
$m = \lfloor k/12 \rfloor$ otherwise, let $C$ be the $m \times m$ matrix
$\bigl(c_i(j)/\sigma_{k-12i-1}(0)\bigr)_{1 \le i, j \le m}$, and let
$(\gamma_1, \dots, \gamma_m) = (\sigma_{k-1}(1), \dots, \sigma_{k-1}(m))\, C^{-1}$. Then for every
$n \ge 1$, $\sigma_{k-1}(n) \equiv
\sum_{i=1}^m \bigl(\gamma_i/\sigma_{k-12i-1}(0)\bigr)\, c_i(n) \pmod{N'_k}$.

## Sources

- Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of Integer Sequences 29 (2026), Article 26.5.1, Corollary 3 (`jis-2026-26.5.1-cor-3`).
