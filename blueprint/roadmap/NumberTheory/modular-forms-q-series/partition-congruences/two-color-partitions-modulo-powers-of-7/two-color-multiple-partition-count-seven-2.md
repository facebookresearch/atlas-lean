# Generating functions for $p_{1,7^{2k-1}}$ on progressions

Let $p_{1,\ell}(n)$ be the
number of 2-color partitions of $n$ in which the parts of the second color are multiples of
$\ell$, let $f_k = \prod_{n \ge 1} (1 - q^{kn})$ in $\mathbb{Q}[[q]]$, and let $y^{(2k-1)}_\beta$
be the coefficient vectors for odd powers of $7$. For all $k \ge 1$ and $\beta \ge 0$, with
$N = 7^{2k+\beta-1}$,

$$\sum_{n \ge 0} p_{1,7^{2k-1}}\Bigl(N n + \frac{16 N + 7^{2k-1} + 1}{24}\Bigr) q^n
= \sum_{i=1}^{N} y^{(2k-1)}_{\beta+1,i}\, q^{i-1} \frac{f_7^{4i-1}}{f_1^{4i+1}}$$

as formal power series over $\mathbb{Q}$.

The numerator $16 N + 7^{2k-1} + 1$ is divisible by $24$. The sum over $i$ stops at $N$, above
the support of $y^{(2k-1)}_{\beta+1}$.

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Theorem 2.
