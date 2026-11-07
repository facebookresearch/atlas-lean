# Trivariate generating function for symmetric valleys in compositions

For a composition
$c$ write $\ell(c)$ for its number of parts, $\mathrm{sv}(c)$ for the number of symmetric
valleys and $\mathrm{dsv}(c)$ for the symmetric valley depth sum of its sequence of parts. In
the ring $\mathbb{Z}[y, p, d][[x]]$ of formal power series in $x$ whose coefficients are
polynomials in $y, p, d$ with integer coefficients,

$$
\sum_{n \ge 0} \sum_{c \models n} x^n y^{\ell(c)} p^{\mathrm{sv}(c)} d^{\mathrm{dsv}(c)} =
\frac{1}{1 - \sum_{a \ge 1} \frac{x^a y}{1 - y^2 x^{a+1}
\sum_{b=1}^{a-1} (p d^{a-b} - 1) x^{b-1}}},
$$

where $c \models n$ ranges over the compositions of $n$. Precisely: for every $n \ge 0$ the
coefficients of $x^n$ on the two sides agree when the sum over $a$ is restricted to
$1 \le a \le n$ (the terms with $a > n$ do not contribute to them). The inner sum equals
$p(x^{a-1} - d^{a-1})/(x/d - 1) - (x^{a-1} - 1)/(x - 1)$.

Corrected reading: the paper prints $(p x^{a-1} - d^{a-1})/(x/d - 1)$, with $p$ on the first
term only; that is false (at $n = 3$ it gives the composition $111$ a symmetric valley of depth
$0$). The corrected term $p(x^{a-1} - d^{a-1})/(x/d - 1)$ is the penultimate line of the
paper's proof, $x^a y^2 p d^a ((x/d)^a - x/d)/(x/d - 1)$, and agrees with the paper's
specialization $d = 1$, $(x^{a-1} - 1)(p - 1)/(x - 1)$.

## Sources

- Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65, Theorem 3 (`integers-2026-A65-thm-3`).
