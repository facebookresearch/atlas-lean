# Two-color partitions with one color restricted to multiples

For natural numbers $\ell$
and $n$, let $p(m)$ be the number of partitions of $m$, and define

$$
p_{1,\ell}(n) = \sum_{j=0}^{\lfloor n/\ell \rfloor} p(n - \ell j)\, p(j).
$$

For $\ell > 0$ this is the number of 2-color partitions of $n$ in which the parts of the second
color are multiples of $\ell$, that is, the coefficient of $q^n$ in $1/(f_1 f_\ell)$, where
$f_m = \prod_{j \ge 1} (1 - q^{mj})$. For $\ell = 0$ the bound $\lfloor n/0 \rfloor$ is taken to
be $0$, so $p_{1,0}(n) = p(n)$; this is a convention with no generating-function meaning. The
source uses $\ell = 7^k$.

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Section 1.
