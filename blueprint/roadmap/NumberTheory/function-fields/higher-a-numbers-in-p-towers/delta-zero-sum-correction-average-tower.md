# The linear coefficient of Proposition 5 vanishes at $\tau$

Let $p$ be a prime and $d$ a
divisor of $p - 1$, let $\tau = (p + 1)/d$, and let $\tau_D$ be the denominator of $\tau$ in
lowest terms. Let $L$ be the order of $p$ modulo the prime-to-$p$ part of the denominator of
$\tau^{-1}$ (the period of the base-$p$ expansion of $\tau^{-1}$), and let $\overline{\tau^{-1}}$
be the average of the repeating base-$p$ digits of $\tau^{-1}$. For $e \ge 0$ let
$F_{\tau^{-1}}(e) = \sum_{k=1}^{\lfloor \tau^{-1} p^e \rfloor \bmod \tau_D p}
(\delta_0(k) - \frac12 (1 - 1/p)(1 - 1/\tau_D))$, where $\delta_0(k)$ is $0$ if $p \mid k$ and
$\delta(k)$ otherwise, $\delta$ being the rounding indicator. Then

$$\frac1L \sum_{e=1}^{L} F_{\tau^{-1}}(e) - \frac{\overline{\tau^{-1}}}{2p} (1 - 1/\tau_D) = 0.$$

This says that the linear coefficient in Proposition 5 vanishes at $\tau$; the delay of
$\tau^{-1}$ is $0$, so the average of $F_{\tau^{-1}}$ is taken over $1 \le e \le L$.

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Proposition 6.
