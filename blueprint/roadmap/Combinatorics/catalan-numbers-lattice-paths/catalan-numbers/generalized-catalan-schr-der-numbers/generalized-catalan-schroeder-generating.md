# Generating function of the generalized Catalan–Schröder numbers

Let $R$ be a commutative
ring, let $s, t, p \in R$, and let $(a_n)_{n \ge 0}$ be a sequence in $R$ with $a_0 = 1$,
$a_1 = p$ and

$$a_n = s\,a_{n-1} + t \sum_{k=0}^{n-3} a_{k+1}\,a_{n-k-2} \qquad (n \ge 2).$$

Let $g$ and $f$ be formal power series over $R$ with

$$(1 - (s - 2t)X)\,g = 1 + (p - s + t)X, \qquad (1 - (s - 2t)X)^2 f = tX\,(1 + (p - s + t)X),$$

and let $C(X) = \sum_{n \ge 0} C_n X^n$, where $C_n$ is the $n$-th Catalan number viewed in $R$.
Then $\sum_{n \ge 0} a_n X^n = g \cdot C(f)$, where $C(f)$ is the power series obtained by
substituting $f$ for $X$ in $C$. Since $1 - (s - 2t)X$ is invertible in $R[[X]]$, these
equations determine $g$ and $f$, and $f$ has zero constant term.

Barry prints $f$ without the factor $X$ in $1 + (p - s + t)X$. That version is false: for
$s = 2$, $t = 1$, $p = 2$ the resulting series $g \cdot C(f)$ has coefficient $3$ at $X$, not
$a_1 = 2$. The recurrence forces the factor restored here.

The proof substitutes $f$ into the Catalan equation $C = 1 + X C^2$, shows that $g \cdot C(f)$
satisfies the same quadratic functional equation as $\sum_{n \ge 0} a_n X^n$, and concludes by
comparing coefficients.

## Sources

- Paul Barry, "Generalized Catalan Recurrences, Riordan Arrays, Elliptic Curves, and Orthogonal Polynomials", Journal of Integer Sequences 24 (2021), Article 21.5.1, Proposition lines 367-373, <https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry/barry431.tex>.
