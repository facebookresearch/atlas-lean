# Lu's three-term congruence for $G_k$

Let $k \in \{36, 40, 42, 44, 46, 50\}$.
For $w, n \in \mathbb{N}$ let $\sigma_{-1}(n)$ be $1$ if $n = 0$ and $0$ otherwise; for $w \ge 1$
let $\sigma_{w-1}(0) = -B_w/(2w)$, where $B_w$ is the $w$-th Bernoulli number, and
$\sigma_{w-1}(n) = \sum_{d \mid n} d^{w-1}$ for $n \ge 1$. In $\mathbb{Q}[[q]]$ let
$G_w = \sum_{n \ge 0} \sigma_{w-1}(n) q^n$, let $E_w = G_w/\sigma_{w-1}(0)$ for even $w$, and let
$\Delta = q \prod_{j \ge 1} (1 - q^j)^{24}$; for $i, n \in \mathbb{N}$ write $b_i(n)$ for the
coefficient of $q^n$ in $\Delta^i E_{k-12i}$. Let $N_w = 1$ for $w \le 2$, let $N_w$ be the
absolute value of the numerator of $\sigma_{w-1}(0)$ for $w \ge 3$, and let $N'_k$ be the largest
divisor of $N_k$ that is coprime to $N_{k-12i}$ for every $1 \le i \le \lfloor k/12 \rfloor$. For
rationals $x, y$ and a positive integer $N$, $x \equiv y \pmod{N}$ means that $(x - y)/N$ has
denominator coprime to $N$. Let
$\gamma_2 = 2^{k-1} + 25 - 1/\sigma_{k-13}(0)$ and
$\gamma_3 = 3^{k-1} + 48 \cdot 2^{k-1} + 949 - (2^{k-13} + 25)/\sigma_{k-13}(0) -
(2^{k-1} + 25)/\sigma_{k-25}(0) + 1/\bigl(\sigma_{k-13}(0)\,\sigma_{k-25}(0)\bigr)$. Then
$\sigma_{k-1}(n) \equiv b_1(n) + \gamma_2 b_2(n) + \gamma_3 b_3(n) \pmod{N'_k}$ for every
$n \ge 0$, that is,
$G_k \equiv \Delta E_{k-12} + \gamma_2 \Delta^2 E_{k-24} + \gamma_3 \Delta^3 E_{k-36}
\pmod{N'_k}$ coefficientwise; in particular the congruence holds for every $n \ge 1$.

## Sources

- Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of Integer Sequences 29 (2026), Article 26.5.1, Corollary 7 (`jis-2026-26.5.1-cor-7`).
