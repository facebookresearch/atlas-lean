# Ramanujan's theta function at monomial arguments

For an integer $\varepsilon$ and natural
numbers $a$ and $b$, $f(\varepsilon q^a, \varepsilon q^b)$ is the integer power series in $q$
whose coefficient of $q^n$ is the sum of $\varepsilon^{m^2}$ over the integers $m$ with
$|m| \le n + 1$ and $a \cdot m(m+1)/2 + b \cdot m(m-1)/2 = n$.

When $a + b \ge 1$ the exponent $a \cdot m(m+1)/2 + b \cdot m(m-1)/2$ is at least
$|m|(|m|-1)/2$, so the bound $|m| \le n + 1$ excludes no term and this is Ramanujan's
$f(c, d) = \sum_{m \in \mathbb{Z}} c^{m(m+1)/2} d^{m(m-1)/2}$ at $c = \varepsilon q^a$ and
$d = \varepsilon q^b$; the definition is meant for $a + b \ge 1$. Special cases are
$\psi(q) = f(q, q^3)$ and $f(-q) = f(-q, -q^2)$, which equals
$(q; q)_\infty = \prod_{k \ge 1} (1 - q^k)$.

## Sources

- Sabi Biswas and Nipen Saikia, *Arithmetic Properties of the Coefficients of Some Mock Theta Functions*, INTEGERS 25 (2025), Article A72, Section 2 (definition of `f(c, d)`, Equations (10) and (11)).
