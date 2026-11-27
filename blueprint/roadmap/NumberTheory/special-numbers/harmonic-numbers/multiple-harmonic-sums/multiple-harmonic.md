# Multiple harmonic sums

For natural numbers $p$, $r$ and $n$, the multiple harmonic sum
$H_r^{(n)}$ modulo $p$ is the element

$$H_r^{(n)} = \sum_{0 < k_1 < \cdots < k_n \le r} k_1^{-1} \cdots k_n^{-1}$$

of $\mathbb{Z}/p\mathbb{Z}$, where the sum runs over the strictly increasing $n$-tuples of
integers, equivalently over the $n$-element subsets of $\{1, \dots, r\}$, and $k^{-1}$ is the
following element of $\mathbb{Z}/p\mathbb{Z}$. For $p \ge 1$, let $c \in \{0, \dots, p - 1\}$ be the
residue of $k$ modulo $p$, and let $a$ be the coefficient of $c$ in the Bézout identity
$a c + b p = \gcd(c, p)$ produced by the extended Euclidean algorithm on $(c, p)$; then $k^{-1}$ is
the class of $a$. This is the inverse of $k$ when $\gcd(k, p) = 1$; for other $k$ it is still this
Bézout coefficient, which is $0$ when $p \mid k$ but need not be $0$ otherwise (for $p = 4$ the
class of $2$ is sent to $1$). For $p = 0$, where $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$, $k^{-1}$ is the
sign of $k$; then every factor $k_i^{-1}$ is $1$ and $H_r^{(n)} = \binom{r}{n}$.

In particular $H_r^{(0)} = 1$, and $H_r^{(n)} = 0$ when $n > r$. For a prime $p$ and $r < p$ every
$k_i^{-1}$ is the true inverse modulo $p$.

## Sources

- Sandro Mattarei and Roberto Tauraso, *Congruences of Multiple Sums Involving Sequences Invariant Under the Binomial Transform*, Journal of Integer Sequences 13 (2010), Article 10.5.1, Section 2 (definition of $H_r^{(n)}$), https://cs.uwaterloo.ca/journals/JIS/VOL13/Tauraso/tauraso22.html.
