# Linear fractional pole series

For real numbers $a$ and $c$, this is the power series
$F_{a,c}(u)$ of $\frac{cu}{a - cu}$: it is $\sum_{n \ge 1} (c/a)^n u^n$ if $a \neq 0$, the
constant $-1$ if $a = 0$ and $c \neq 0$, and $0$ (a junk value) if $a = c = 0$. It is $u$
times the summand $\frac{c}{a - cu}$ of $G_g(u) = \frac{c}{a - cu} - \frac{d}{b - du}$ for
the matrix $g$ with rows $(a, b)$ and $(c, d)$.

## Sources

- Ken Kamano, *A Generalization of the Landen Connection Formula and Generalized Poly-Bernoulli Numbers*, INTEGERS 24 (2024), Article A77, Section 2, the function `G_g(t)` before Table 1.
