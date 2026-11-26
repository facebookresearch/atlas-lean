# Repstrings

For natural numbers $b$, $k$, $z$ and $t$, let $\ell$ be the number of base-$b$
digits of $k$. The $b$-repstring is

$$k_b^{(z;t)} = \left\lfloor \frac{k\,(b^{(z+\ell)t} - 1)}{b^{z+\ell} - 1} \right\rfloor,$$

where subtraction is truncated at $0$ and the integer division gives $0$ when the denominator is
$0$. For $z = 0$ it is the $b$-repinteger $k_b^{(t)}$.

For $b \ge 2$ and $k \ge 1$ the division is exact, and $k_b^{(z;t)}$ is the number whose base-$b$
expansion is $k$ written $t$ times with $z$ zeros between consecutive copies.

## Sources

- Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Sections 1 and 4.
