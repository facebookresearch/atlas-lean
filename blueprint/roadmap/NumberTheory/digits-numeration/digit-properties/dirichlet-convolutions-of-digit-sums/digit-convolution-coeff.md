# Digit-convolution coefficients

For a natural number $q$, the base-$q$ digit-convolution
coefficients are the real numbers $a(k)$, $k \ge 0$, given by $a(0) = a(1) = 0$,
$a(2) = \frac{(q - 1)^2}{24 \log^2 q}$ and, for every $k \ge 3$,

$$
a(k) = a(k - 1) \cdot \frac{q - 1}{2 \log q}
\sum_{j=0}^{2k-3} \binom{2k-3}{j} \frac{(-1)^j}{j + 2},
$$

where $\log$ is the natural logarithm, with $\log 0 = 0$, and division by $0$ is read as $0$ (this
matters only for $q \le 1$). The values $a(0) = a(1) = 0$ are a convention; only the coefficients
$a(k)$ with $k \ge 2$ enter the asymptotic formulas.

These are the coefficients of the source's Theorem 3 divided by $24 \log^2 q$: the source writes
$a(2) = (q - 1)^2$, with the same recurrence, and puts the factor $1/(24 \log^2 q)$ in front of
$a(k)$ in its asymptotic formula.

## Sources

- Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43, Theorem 3 (definition of $a(k)$).
