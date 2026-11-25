# Euler–Maclaurin formula

Let $a < b$ be integers, let $p \ge 1$ be a natural number, and
let $f : \mathbb{R} \to \mathbb{R}$ be $p$ times continuously differentiable on $[a, b]$, its
derivatives $f^{(k)}$ being taken relative to $[a, b]$ (one-sided at the endpoints). Let $B_j$
be the Bernoulli numbers with $B_1 = -\tfrac{1}{2}$. Then there are $1$-periodic functions
$P_m : \mathbb{R} \to \mathbb{R}$ for $m \ge 0$ such that $P_p$ agrees on $[0, 1)$ with the
Bernoulli polynomial $\sum_{j=0}^{p} \binom{p}{j} B_j x^{p-j}$, and
$\sum_{n=a}^{b} f(n) = I + E + R$, where $I = \int_a^b f(x)\,dx + \frac{f(a) + f(b)}{2}$,
$E = \sum_{k=1}^{\lfloor p/2 \rfloor} \frac{B_{2k}}{(2k)!} (f^{(2k-1)}(b) - f^{(2k-1)}(a))$
and $R = \frac{(-1)^{p+1}}{p!} \int_a^b P_p(x) f^{(p)}(x)\,dx$.

## Sources

- https://en.wikipedia.org/wiki/Euler%E2%80%93Maclaurin_formula.
