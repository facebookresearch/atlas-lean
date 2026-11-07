# Divisor-sum formula for the length-four run count

For a natural number $B$, let $A_B(4)$
be the number of integer tuples $(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and
$(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at least $4$. For integers $x, y$
let $T_B(x, y)$ be the number of integer triples $(a, b, c) \in [-B, B]^3$ with $x \mid a$,
$y \mid b$, $x + y \mid c$ and $x + 2y \mid a + b + c$, and let $T'_B(x, y)$ be the number of
integer triples $(\alpha, \beta, \gamma)$ with $|\alpha| \le \lfloor B/|x| \rfloor$,
$|\beta| \le \lfloor B/|y| \rfloor$, $|\gamma| \le \lfloor B/|x+y| \rfloor$ and
$x + 2y \mid x\alpha + y\beta + (x+y)\gamma$. Then

$$A_B(4) = \sum_{x, y} \left(T_B(x, y) - 1\right) = \sum_{x, y} \left(T'_B(x, y) - 1\right),$$

where both sums run over the integers $x, y \in [-B, B]$ with $x \ne 0$, $y \ne 0$, $x + y \ne 0$
and $x + 2y \ne 0$.

The second form comes from writing $a = x\alpha$, $b = y\beta$, $c = (x+y)\gamma$; it is the
paper's $\sum \chi_{x,y}(\alpha, \beta, \gamma)$.

## Sources

- Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 7.
