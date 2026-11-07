# Solutions of a linear congruence

Let $a$ and $b$ be integers, let $m$ be a positive
integer, and let $d = \gcd(a, m)$. The congruence $a x \equiv b \pmod{m}$ has an integer
solution if and only if $d \mid b$. If $d \mid b$, then exactly $d$ of the numbers
$x \in \{0, 1, \dots, m - 1\}$ are solutions. Moreover, if $x_0$ is a solution, then an integer
$x$ is a solution if and only if $x \equiv x_0 + u \cdot (m / d) \pmod{m}$ for some integer $u$
with $0 \le u \le d - 1$.

## Sources

- Jourdan D'orville, Kai An Sim, Kok Bin Wong, and Chee Kit Ho, *Modular Generalizations of Schur Numbers*, INTEGERS 25 (2025), Article A62, Theorem 3, quoting a textbook result ([3]) (`integers-2025-A62-thm-3`).
