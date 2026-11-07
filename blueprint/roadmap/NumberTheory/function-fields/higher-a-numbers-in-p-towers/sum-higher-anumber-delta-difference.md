# Sum of $\delta$ between the $\gamma$- and $\tau$-cutoffs

Let $p$ be a prime, let $d$
be a divisor of $p - 1$ and let $r \ge 1$ be an integer. Write $\tau = (p + 1)/d$,
$\gamma = ((p - 1) r + (p + 1))/d$ and $\tau_D$ for the denominator of $\tau$ in lowest terms;
let $\delta$ be the rounding indicator, and for a rational $y$ let $L_y$ be the period, $D_y$
the delay and $\bar y$ the average repeating digit of the base-$p$ expansion of $y$, and let
$F_y(e)$ be the $\delta_0$ correction sum of Lemma 9. Put $D = D_{\gamma^{-1}}$,
$L = L_{\gamma^{-1}}$, $s = \max(D + 1, 0)$ and
$\bar F = \frac{1}{L} \sum_{e=s}^{s+L-1} F_{\gamma^{-1}}(e)$. Then there is a function
$C : \mathbb{N} \to \mathbb{Q}$ such that $C(n + \operatorname{lcm}(L_{\tau^{-1}}, L)) = C(n)$
for every natural number $n \ge D$, and for every natural number $n \ge D$,

$$\sum_{\lfloor p^n/\gamma \rfloor < i \le \lfloor p^n/\tau \rfloor} \delta(i) =
\frac{1}{2} (\tau^{-1} - \gamma^{-1}) \left(1 - \frac{1}{\tau_D}\right) p^n +
\left(\frac{\overline{\gamma^{-1}}}{2p} \left(1 - \frac{1}{\tau_D}\right) - \bar F\right) n +
C(n).$$

The paper's explicit $B$ functions are replaced by the existential $C$.

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Corollary 5 (`integers-2026-A78-cor-5`).
