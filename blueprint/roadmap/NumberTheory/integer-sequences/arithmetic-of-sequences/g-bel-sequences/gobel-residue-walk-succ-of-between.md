# Recurrence of the residue walk at interior values

Let $p$, $l$ and $n$ be natural numbers
with $n \ge 1$, write $\tilde g_l$ for the residue walk of $p$ starting at $l$, and write
$\left(\frac{a}{p}\right)$ for the Jacobi symbol. If $0 < \tilde g_l(n) < p$, then

$$\tilde g_l(n+1) = \max\bigl(0, \tilde g_l(n) + (\tfrac{n}{p})(\tfrac{\tilde g_l(n)}{p})\bigr).$$

The maximum with $0$ records the conversion of the integer sum back to a natural number; the sum
is never negative because $\tilde g_l(n) \ge 1$.

## Sources

- Yuh Kobayashi and Shin-ichiro Seki, *A Note on Non-Integrality of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 29 (2026), Article 26.3.8, Section 2 definition of `tilde g_l`.
