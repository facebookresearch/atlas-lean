# The square-splitting totient function

Let $A(n)$ be the set of square-splitting divisors
of $n$, and let $\varphi_\star$ be any integer-valued arithmetic function with
$\sum_{d \in A(n)} \varphi_\star(d) = n$ for every $n \ge 1$. Then $\varphi_\star$ is
multiplicative and $\varphi_\star(1) = 1$. For every prime $p$, $\varphi_\star(p) = p - 1$, and
for every $b \ge 1$, $\varphi_\star(p^{2b}) = (p^2 - 1)\,p^{2b-2}$ and
$\varphi_\star(p^{2b+1}) = (p - 1)(p^2 - 1)\,p^{2b-2}$. Moreover, for every $n \ge 1$,

$$\varphi_\star(n) = \varphi(u(n))\,v(n)^2 \prod_{p \mid v(n)} \left(1 - \frac{1}{p^2}\right),$$

where $\varphi$ is Euler's totient function, $u(n)$ is the product of the primes dividing $n$ to
an odd power and $v(n)$ is the positive integer with $n = u(n)\,v(n)^2$.

## Sources

- Champak Talukdar and Helen K. Saikia, *A Square-Splitting A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 7 (`integers-2026-A56-thm-7`).
