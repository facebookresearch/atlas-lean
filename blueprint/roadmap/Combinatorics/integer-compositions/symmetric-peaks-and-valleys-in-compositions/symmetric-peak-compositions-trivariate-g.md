# Trivariate generating function for symmetric peaks in compositions

For a composition
$c$ write $\ell(c)$ for its number of parts, $\mathrm{sp}(c)$ for the number of symmetric peaks
and $\mathrm{hsp}(c)$ for the symmetric peak height sum of its sequence of parts. In the ring
$\mathbb{Z}[y, q, h][[x]]$ of formal power series in $x$ whose coefficients are polynomials in
$y, q, h$ with integer coefficients,

$$
\sum_{n \ge 0} \sum_{c \models n} x^n y^{\ell(c)} q^{\mathrm{sp}(c)} h^{\mathrm{hsp}(c)} =
\frac{1}{1 - \sum_{a \ge 1} \frac{x^a y}{1 - y^2 x^{2a+1} \left(\frac{qh}{1 - hx} -
\frac{1}{1 - x}\right)}},
$$

where $c \models n$ ranges over the compositions of $n$ and
$\frac{qh}{1 - hx} - \frac{1}{1 - x}$ stands for the series $\sum_{j \ge 0} (q h^{j+1} - 1) x^j$.
Precisely: for every $n \ge 0$ the coefficients of $x^n$ on the two sides agree when the sum
over $a$ is restricted to $1 \le a \le n$ (the terms with $a > n$ do not contribute to them).

## Sources

- Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65, Theorem 1.
