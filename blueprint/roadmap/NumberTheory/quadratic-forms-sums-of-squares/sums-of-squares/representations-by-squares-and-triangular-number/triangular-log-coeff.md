# Logarithmic coefficients of the triangular theta series

For a natural number $n$, let
$b_n$ be the rational number
$b_n = \sum_{d \mid n,\ n/d \text{ odd}} 1/d - \sum_{d \mid n,\ n/d \text{ even}} 1/d$, where $d$
runs over the positive divisors of $n$; for $n = 0$ the sums are taken to be empty, so $b_0 = 0$.

With $\psi(q) = \sum_{m \ge 0} q^{m(m+1)/2}$, the expansion
$\log \psi(q) = \sum_{m \ge 1} \log(1 - q^{2m}) - \sum_{m \ge 1} \log(1 - q^{2m-1})$ in the proof
of Theorem 2 shows that $b_n$ is the coefficient of $q^n$ in $\log \psi(q)$. The printed formula
of Theorem 2 has the parity condition on $d$ instead of $n/d$, which gives $b_2 = 1/2$ instead
of $-1/2$.

## Sources

- Alegri and Christopher, *On Formulas, Recurrences, and Congruences for Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS 26 (2026), Article A93, Theorem 2 and its proof.
