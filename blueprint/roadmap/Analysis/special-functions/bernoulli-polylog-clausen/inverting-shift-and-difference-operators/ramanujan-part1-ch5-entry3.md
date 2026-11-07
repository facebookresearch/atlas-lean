# Eulerian-polynomial inverse of a shift-plus-multiple operator

Let $A(n, k)$ be the
Eulerian numbers, given by $A(0, 0) = 1$, $A(0, k) = 0$ for $k \ge 1$ and
$A(n + 1, k) = (k + 1) A(n, k) + (n + 1 - k) A(n, k - 1)$, the last term read as $0$ when
$k = 0$. For $p \in \mathbb{C}$ set $\psi_0(p) = 1$ and
$\psi_n(p) = \sum_{k=0}^{n-1} A(n, k) (-p)^k$ for $n \ge 1$. For a sequence $a_0, a_1, \ldots$
of complex numbers, $h \in \mathbb{C}$ and a polynomial $\varphi \in \mathbb{C}[x]$, write
$E_{a,h} \varphi = \sum_{n=0}^{\deg \varphi} a_n h^n \varphi^{(n)}$, where $\varphi^{(n)}$ is the
$n$-th derivative. Fix $p \in \mathbb{C}$ with $p \ne -1$ and put
$c_n = \frac{(-1)^n \psi_n(p)}{n! \, (p + 1)^{n + 1}}$. Then:
(1) for every $h \in \mathbb{C}$ and every $\varphi \in \mathbb{C}[x]$, the polynomial
$f = E_{c,h} \varphi$ satisfies $f(x + h) + p f(x) = \varphi(x)$ as polynomials in $x$;
(2) if a sequence $a$ of complex numbers is such that $f = E_{a,h} \varphi$ satisfies
$f(x + h) + p f(x) = \varphi(x)$ for every $h \in \mathbb{C}$ and every $\varphi \in \mathbb{C}[x]$,
then $a_n = c_n$ for every $n \ge 0$.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5. Proves `Wanted` entry `ramanujan_part1_ch5_entry3`.
