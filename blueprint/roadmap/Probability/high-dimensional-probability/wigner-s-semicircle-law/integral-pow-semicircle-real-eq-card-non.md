# The moments of the semicircle law count noncrossing pair partitions

For every $n \ge 0$, the $n$-th moment of the semicircle distribution
$\sigma(dx) = \frac{1}{2\pi}\sqrt{4 - x^2}\,\mathbf{1}_{|x| \le 2}\,dx$ is the number of noncrossing
pair partitions of $\{1, \dots, n\}$:

$$\int x^n \, d\sigma(x) = \#\{\pi \in NC(n) : \text{every block of } \pi \text{ has two elements}\},$$

which is $C_{n/2}$ for $n$ even and $0$ for $n$ odd.

This is the form in which the semicircle law appears at the end of two different arguments. In the
moment method for Wigner matrices, the Wigner words of length $n + 1$ that dominate
$\frac{1}{N}\mathbb{E}\operatorname{tr} X_N^{n}$ correspond to noncrossing pair partitions
(Anderson, Guionnet and Zeitouni, Proposition 2.1.11). In the free central limit theorem, all free
cumulants of $N^{-1/2}(a_1 + \dots + a_N)$ except the second vanish in the limit, so the
moment-cumulant formula over noncrossing partitions leaves exactly the noncrossing pair partitions
(Lemma 5.3.32 there).

## Informally uses

- [The even moments of the semicircle distribution are the Catalan numbers](integral-pow-two-mul-semicircle-real.md):
  the analytic side, $\int x^{2k}\,d\sigma = C_k$.
- [The odd moments of the semicircle distribution vanish](integral-pow-two-mul-add-one-semicircle.md):
  the odd analytic side.
- [Counting noncrossing pair partitions](../../../Combinatorics/set-partitions/noncrossing-partitions/noncrossing-pair-partitions-and-the-catalan-count/card-noncrossing-pair-partition.md):
  the combinatorial side.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §2.1.1, equation (2.1.4); Proposition 2.1.11; proof of Lemma 5.3.32.
