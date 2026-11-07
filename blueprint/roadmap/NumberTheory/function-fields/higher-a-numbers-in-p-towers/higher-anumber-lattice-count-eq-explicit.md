# Explicit linear term and period for higher $a$-numbers

Let $p$ be a prime, let $d$ be a
natural number dividing $p - 1$, let $r \ge 1$, let $\tau = (p + 1)/d$ and
$\gamma = ((p - 1) r + (p + 1))/d$, let $\tau_D$ be the denominator of $\tau$ in lowest terms, let
$\delta_0$ be the variant of the rounding indicator for $p$ and $d$, and for each natural number
$n$ let $A_r(n)$ be the lattice-point count for the $r$-th higher $a$-number at level $n$. Put
$x = \gamma^{-1}$. Let $L$ be the period of the base-$p$ expansion of $x$ (the order of $p$
modulo the prime-to-$p$ part of the denominator of $x$), let $D = -v_p(x)$ be its delay, let
$\bar{x}$ be the average of its repeating digits, put $e_0 = \max(D + 1, 0)$, and for a natural
number $e$ let

$$F(e) = \sum_{k=1}^{\lfloor x p^e \rfloor \bmod \tau_D p}
\left(\delta_0(k) - \tfrac{1}{2} (1 - 1/p)(1 - 1/\tau_D)\right).$$

With

$$\lambda_r = \frac{1}{L} \sum_{e=e_0}^{e_0 + L - 1} F(e) -
\frac{\bar{x}}{2p} \left(1 - \frac{1}{\tau_D}\right),$$

there is a function $\nu_r$ from the natural numbers to the rationals such that
$A_r(n) = \frac{1}{2} (\tau^{-1} - \gamma^{-1}) p^{2n} + \lambda_r n + \nu_r(n)$ for every natural
number $n$, $\nu_r(n + \operatorname{lcm}(L, 2)) = \nu_r(n)$ for every natural number $n \ge D$,
and $\operatorname{lcm}(L, 2) \mid 2L'$ for every $L' > 0$ such that $\nu_r(n + L') = \nu_r(n)$
for all natural numbers $n \ge D$.

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Theorem 4 (`integers-2026-A78-thm-4`).
