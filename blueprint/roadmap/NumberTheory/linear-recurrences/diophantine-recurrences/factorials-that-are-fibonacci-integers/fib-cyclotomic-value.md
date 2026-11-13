# Fibonacci cyclotomic values

For a natural number $m$, $\Phi_m$ is the rational number
$\prod_{d \mid m} F_{m/d}^{\mu(d)}$, where $d$ runs over the positive divisors of $m$, $F_k$ is the
$k$-th Fibonacci number and $\mu$ is the Möbius function. For $m > 1$ this is the value
$\Phi_m(\alpha, \beta)$ of the homogenized $m$-th cyclotomic polynomial at the roots
$\alpha, \beta$ of $x^2 - x - 1$.

At $m = 1$ the formula gives $1$, not $\Phi_1(\alpha, \beta) = \alpha - \beta = \sqrt{5}$, and
$m = 0$ is treated as having no divisors, so $\Phi_0 = 1$.

## Sources

- Florian Luca, *`F_4 F_5^6 F_7 F_8^4 F_9 F_{10}^2 F_{12}^5 F_{14} F_{15}^{-1} F_{18} F_{24} F_{30} = 36!`*, INTEGERS 24 (2024), Article A72, Section 2.
