# Reduced forms of a given discriminant

For an integer $d$, $R(d)$ is the finite set of
integer triples $(a, b, c)$ such that the binary quadratic form $a x^2 + b x y + c y^2$ is Gauss
reduced (that is, $a > 0$, $b^2 - 4ac < 0$, $|b| \le a \le c$, and $b \ge 0$ whenever $|b| = a$ or
$a = c$) and has discriminant $b^2 - 4ac = d$. In particular $R(d)$ is empty when $d \ge 0$.

The set is computed by a finite search: a reduced form satisfies $-d = 4ac - b^2 \ge 3a^2$, so
$1 \le a \le \lfloor \sqrt{-d} \rfloor$ and $|b| \le a$, and $c = (b^2 - d) / (4a)$ is determined
by $a$ and $b$.

## Sources

- Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1.
