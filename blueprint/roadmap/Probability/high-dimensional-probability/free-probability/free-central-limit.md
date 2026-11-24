# The free central limit theorem

Let $(A, \varphi)$ be a noncommutative probability space whose functional is a tracial state
($\varphi(1) = 1$, $\varphi(xy) = \varphi(yx)$, $\varphi(x^* x) \ge 0$), and let $a_0, a_1, \dots$
be [free](are-free.md) self-adjoint elements with $\varphi(a_i) = 0$, $\varphi(a_i^2) = 1$ and
$\sup_i |\varphi(a_i^k)| < \infty$ for every $k$. Then

$$X_N = \frac{1}{\sqrt{N}} \sum_{i=0}^{N-1} a_i$$

converges in moments to the standard semicircle law: for every $p$, $\varphi(X_N^p)$ tends to the
number of noncrossing pair partitions of $\{1, \dots, p\}$, which is $\int x^p \, d\sigma(x)$.

Proof in the source: by [additivity of free cumulants](free-cumulant-add-of-are-free.md),
$\kappa_p(X_N) = N^{-p/2} \sum_i \kappa_p(a_i)$, which tends to $0$ for $p \ge 3$, while
$\kappa_1(X_N) = 0$ and $\kappa_2(X_N) = 1$; the moment-cumulant formula then leaves only the
noncrossing pair partitions. The hypotheses are met, for example, by a free semicircular family on the full Fock
space.

## Informally uses

- [Free cumulants are additive for free variables](free-cumulant-add-of-are-free.md): the scaling of
  the cumulants of $X_N$.
- [Moment-cumulant formula](moment-eq-sum-noncrossing-prod-free-cumu.md): to return from the limit
  cumulants to the limit moments.
- [Counting noncrossing pair partitions](../../../Combinatorics/set-partitions/noncrossing-partitions/noncrossing-pair-partitions-and-the-catalan-count/card-noncrossing-pair-partition.md):
  the limit moments.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Lemma 5.3.32 and its proof.
