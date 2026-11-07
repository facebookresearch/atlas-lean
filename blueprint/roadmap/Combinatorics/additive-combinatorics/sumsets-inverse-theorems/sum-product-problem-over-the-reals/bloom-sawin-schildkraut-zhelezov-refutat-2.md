# The real sum-product exponent is less than 2 (Bloom–Sawin–Schildkraut–Zhelezov)

The real
sum-product exponent $C$ satisfies $C < 2$. Here, for a finite set $A \subset \mathbb{R}$,
$A + A$ and $A \cdot A$ are the sets of sums $a + b$ and products $ab$ with $a, b \in A$, and
$M(A) = \max(|A + A|, |A \cdot A|)$; for $n \ge 2$, $m(n)$ is the minimum of
$\log M(A) / \log |A|$ over all $A \subset \mathbb{R}$ with $|A| = n$; and
$C = \liminf_{n \to \infty} m(n)$.

This refutes the historical Erdős–Szemerédi conjecture $C = 2$ for real sets: Bloom, Sawin,
Schildkraut and Zhelezov (arXiv:2605.28781) construct arbitrarily large finite sets
$A \subset \mathbb{R}$ with $M(A) \le |A|^{2 - c}$ for an absolute constant $c > 0$.

## Sources

- Paul Erdős and Endre Szemerédi, On sums and products of integers, Studies in Pure Mathematics (1983), 213-218, https://doi.org/10.1007/978-3-0348-5438-2_19; György Elekes, On the number of sums and products, Acta Arithmetica 81 (1997), no. 4, 365-367, https://doi.org/10.4064/aa-81-4-365-367; József Solymosi, On the number of sums and products, Bulletin of the London Mathematical Society 37 (2005), no. 4, 491-494, https://doi.org/10.1112/S0024609305004261; József Solymosi, Bounding multiplicative energy by the sumset, Advances in Mathematics 222 (2009), no. 2, 402-408, https://doi.org/10.1016/j.aim.2009.04.006; Misha Rudnev and Sophie Stevens, An update on the sum-product problem, Mathematical Proceedings of the Cambridge Philosophical Society 173 (2022), no. 2, 411-430, https://arxiv.org/abs/2005.11145; Thomas F. Bloom, A history of the sum-product problem, https://thomasbloom.org/notes/sumproduct.html; Adam Cushman, A note on the sum-product problem and the convex sumset problem, arXiv:2512.13849 (2025), https://arxiv.org/abs/2512.13849; Thomas F. Bloom, Will Sawin, Carl Schildkraut, and Dmitrii Zhelezov, The sum-product conjecture is false for real numbers, arXiv:2605.28781 (2026), https://arxiv.org/abs/2605.28781; Optimization Problems, record 84b, Sum-product exponent for the reals, tables of known upper and lower bounds (source commit 2c1968cd520b60f1cf3cf50749f7285e800e4e15), https://github.com/teorth/optimizationproblems/blob/2c1968cd520b60f1cf3cf50749f7285e800e4e15/constants/84b.md. Moved from `OpenConjectures/Combinatorics/RealSumProductExponent`.
