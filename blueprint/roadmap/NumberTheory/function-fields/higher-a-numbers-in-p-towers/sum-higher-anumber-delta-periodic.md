# Eventual periodicity of the $\delta$ sums

Let $p$ be a prime and $d$ a divisor of
$p - 1$; let $\delta$ be the rounding indicator, $\tau_D$ the denominator of $\tau = (p + 1)/d$
in lowest terms, and $F_y(e)$ the $\delta_0$ correction sum of Lemma 9. Let $x$ be a positive
rational such that the prime-to-$p$ part $x_D$ of the denominator of $x$ equals $\tau_D$, and
write $D = D_{x^{-1}}$, $L = L_{x^{-1}}$ and $\overline{x^{-1}}$ for the delay, the period and
the average repeating digit of the base-$p$ expansion of $x^{-1}$. Then
$F_{x^{-1}}(e + L) = F_{x^{-1}}(e)$ for every natural number $e \ge D + 1$. Moreover, with
$s = \max(D + 1, 0)$ and $\bar F = \frac{1}{L} \sum_{e=s}^{s+L-1} F_{x^{-1}}(e)$, there is a
function $B : \mathbb{N} \to \mathbb{Q}$ with $B(n + L) = B(n)$ for every natural number
$n \ge D$ such that for every natural number $n \ge D$,

$$\sum_{i=1}^{\lfloor p^n/x \rfloor} \delta(i) =
\frac{1}{2} x^{-1} \left(1 - \frac{1}{\tau_D}\right) p^n +
\left(\bar F - \frac{\overline{x^{-1}}}{2p} \left(1 - \frac{1}{\tau_D}\right)\right) n + B(n).$$

The paper's explicit $B$ (Equation (6)) is replaced by an existential.

## Sources

- Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Proposition 5.
