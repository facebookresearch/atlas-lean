# The even moments of the semicircle distribution are the Catalan numbers

For every $k \in \mathbb{N}$, the semicircle distribution $\sigma$ satisfies

$$\int x^{2k} \, d\sigma(x) = \frac{1}{2\pi}\int_{-2}^{2} x^{2k} \sqrt{4 - x^2} \, dx = C_k
= \frac{1}{k + 1}\binom{2k}{k}.$$

So $\sigma$ has variance $C_1 = 1$, fourth moment $C_2 = 2$ and sixth moment $C_3 = 5$. In the
moment method for Wigner's semicircle law, $C_k$ counts the non-crossing pairings that dominate
$\frac{1}{n}\,\mathbb{E}\operatorname{tr}(W_n / \sqrt{n})^{2k}$, and this identity
recognises the limit as $\sigma$.

Proof: substitute $x = 2\cos\theta$ with $\theta \in [0, \pi]$, which turns the integral into
$\frac{2^{2k+2}}{2\pi}\int_0^\pi \cos^{2k}\theta \sin^2\theta \, d\theta$, and evaluate
$\int_0^\pi \cos^{2k}\theta \, d\theta = \pi \binom{2k}{k} / 4^k$ with the reduction formula
$\int_0^\pi \cos^{n+2} = \frac{n+1}{n+2}\int_0^\pi \cos^n$.

## Informally uses

- [Catalan numbers](../../../Combinatorics/catalan-numbers-lattice-paths/catalan-numbers/catalan-numbers/README.md):
  the closed form $C_k = \binom{2k}{k}/(k+1)$ that the integral evaluates to.

## Background

- [Stieltjes moment problem](../../../Analysis/harmonic-analysis/integral-transforms/stieltjes-moment-problem/README.md):
  background on moment determinacy. Since $C_k \le 4^k$, the semicircle distribution is
  determined by its moments, which is what lets convergence of moments prove the semicircle law.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, §2.4.2, Exercise 2.4.9 (the moments; the
  Catalan numbers $C_{k/2}$ are defined in (2.88)), and Lemma 2.3.15 (non-crossing cycles counted
  by Catalan numbers).
- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §2.1.1.
