# Generating functions for $p_{1,7^{2k}}$ on progressions

Let $p_{1,\ell}(n)$ be the
number of 2-color partitions of $n$ in which the parts of the second color are multiples of
$\ell$, let $f_k = \prod_{n \ge 1} (1 - q^{kn})$ in $\mathbb{Q}[[q]]$, and let $y^{(2k)}_\beta$ be
the coefficient vectors for even powers of $7$. For all $k \ge 1$ and $\beta \ge 0$, with
$N = 7^{2k+2\beta-1}$,

$$\sum_{n \ge 0} p_{1,7^{2k}}\Bigl(N n + \frac{10 N + 7^{2k} + 1}{24}\Bigr) q^n
= \sum_{i=1}^{7N} y^{(2k)}_{2\beta+1,i}\, q^{i-1} \frac{f_7^{4i-2}}{f_1^{4i}}$$

and

$$\sum_{n \ge 0} p_{1,7^{2k}}\Bigl(7N n + \frac{22 \cdot 7N + 7^{2k} + 1}{24}\Bigr) q^n
= \sum_{j=1}^{49N} y^{(2k)}_{2\beta+2,j}\, q^{j-1} \frac{f_7^{4j}}{f_1^{4j+2}}$$

as formal power series over $\mathbb{Q}$.

Both numerators are divisible by $24$. The sums stop at $7N$, resp. $49N$, above the supports of
the vectors.

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Theorem 3.
