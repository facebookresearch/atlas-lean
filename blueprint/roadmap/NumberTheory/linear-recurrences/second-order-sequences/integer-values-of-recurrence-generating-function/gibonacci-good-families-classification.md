# Classification of the families of good values for a Gibonacci generating function

For integers $a$ and $b$, a rational number $x$ is good for $(a, b)$ when $1 - x - x^2 \ne 0$ and $G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}$ is an integer. For a pair of integers $(p, q)$, its family consists of the consecutive pairs $(H_n, H_{n+1})$, $n \in \mathbb{Z}$, of the two-sided integer sequence with $H_0 = p$, $H_1 = q$ and $H_{n+2} = H_{n+1} + H_n$ for every integer $n$. Let $a$ and $b$ be integers with $(a, b) \ne (0, 0)$. Then the following hold.

First, for all integers $M$ and $k$ with $k \ne 0$ and $M^2 = 5k^2 + (2b - 6a)k + (a - b)^2$, the rational number $\frac{a - b - k + M}{2k}$ is good for $(a, b)$.

Second, let $p$ and $q$ be coprime integers with $q \ne 0$ such that $p/q$ is good for $(a, b)$, and suppose that for every pair $(r, s)$ in the family of $(p, q)$ with $s \ne 0$ the rational number $r/s$ is nonzero and is not a zero of $G^{(a,b)}$. Then some pair $(r, s)$ in the family of $(p, q)$ with $s \ne 0$ has $r/s = \frac{a - b - k + M}{2k}$ for integers $M$, $k$ and $N$ with $k \ne 0$,

$$M^2 = 5k^2 + (2b - 6a)k + (a - b)^2 \quad \text{and} \quad M^2 + 3MN + N^2 = a^2 + ab - b^2,$$

and moreover $M^2 \le |a^2 + ab - b^2|$ if $a^2 + ab - b^2 < 0$, while $5M^2 \le a^2 + ab - b^2$ if $a^2 + ab - b^2 > 0$. The second part leaves out the Fibonacci family, which contains $0$, and the family containing a zero of $G^{(a,b)}$.

## Sources

- Michael P. Knapp, *Fibonacci Generating Functions*, Journal of Integer Sequences 27 (2024), Article 24.3.1, Theorem 4.
