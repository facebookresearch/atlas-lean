# Digit-sum arithmetic function

For a natural number $q$, $s_q$ is the arithmetic function
that sends $n$ to $s_q(n)$, the sum of the digits of $n$ in base $q$. Its $k$-th Dirichlet power
is the $k$-fold Dirichlet convolution $s_q^{(k)}$, so $s_q^{(1)} = s_q$ and
$s_q^{(k)} = s_q * s_q^{(k-1)}$ for $k \ge 2$.

For $q \le 1$ the base-$q$ digit expansion is degenerate and $s_q(n) = n$.

## Sources

- Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43, Section 1 (definition of `s_q` and of `s_q^{(k)}`).
