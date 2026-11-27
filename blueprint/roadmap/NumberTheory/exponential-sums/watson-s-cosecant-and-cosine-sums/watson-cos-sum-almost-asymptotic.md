# Almost-asymptotic expansion of Watson's cosine sum

Let $n \ge 2$, $N \ge 2$ and $\nu$ be
natural numbers with $1 \le \nu \le n - 1$, and let

$$
C_n(\nu) = \sum_{l=1}^{n-1} \frac{\cos(2 \pi \nu l / n)}{\sin(\pi l / n)}.
$$

For $r \ge 1$ write

$$
T_r(n, \nu) = \frac{(1 - 2^{1-2r}) \, \pi^{2r-1} B_{2r} \, \cot^{(2r-1)}(\pi \nu / n)}
{(2r)! \, n^{2r-1}},
$$

where $B_{2r}$ is the $2r$-th Bernoulli number and $\cot^{(2r-1)}$ is the $(2r-1)$-st derivative
of the cotangent. Then there is a real number $\lambda$ with $0 < \lambda < 1$ such that

$$
C_n(\nu) = -\frac{2n}{\pi} \log\left(2 \sin\frac{\pi \nu}{n}\right) +
2 \sum_{r=1}^{N-1} T_r(n, \nu) + 2 \lambda \, T_N(n, \nu).
$$

## Sources

- Iaroslav V. Blagouchine, *On a Generalization of Watson’s Trigonometric Sum (On Dowker’s Sum of Order One Half)*, INTEGERS 25 (2025), Article A30, Theorem 3 (printed as Theorem 4).
