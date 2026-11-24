# Linear Laurent coefficient of the height one multiple zeta function

Let $j \ge 1$ be an
integer, write $\zeta(s, \{1\}^{j-1})$ for the height one multiple zeta function and $\zeta_r(s)$
for the multiple Hurwitz zeta function of order $r$. There are complex numbers
$c_0, \dots, c_{j-1}$ and a function $F$ analytic at $s = 1$ such that
$\zeta(s, \{1\}^{j-1}) = \sum_{i=0}^{j-1} c_i (s - 1)^{-(i+1)} + F(s)$ for all $s$ near $1$
with $\operatorname{Re} s > 1$, and

$$-F'(1) = \int_0^1 \bigl((1 - r) \, \zeta_r(j + 2) - \zeta_r(j + 1)\bigr) \, dr - a_{j+1},$$

where $a_{j+1}$ is the coefficient of $s^{j+1}$ in the Taylor expansion of $1/\Gamma(s + 1)$
at $s = 0$.

The number $-F'(1)$ generalizes the first Stieltjes constant $\gamma_1$: for $j = 1$ and
$\operatorname{Re} s > 1$, $\zeta(s, \{1\}^0)$ equals the Riemann zeta function $\zeta(s)$, whose
Laurent expansion at $s = 1$ is $\zeta(s) = \frac{1}{s - 1} + \gamma - \gamma_1 (s - 1) + \cdots$
with Euler's constant $\gamma$, so $-F'(1) = \gamma_1$.

## Sources

- Paul Thomas Young, *Series of Height One Multiple Zeta Functions*, INTEGERS 24 (2024), Article A43, Corollary 3.
