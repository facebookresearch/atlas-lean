# Free cumulants of a moment sequence

For a sequence $m = (m_n)_{n \ge 0}$ of complex numbers, the free cumulants $\kappa_n$, $n \ge 1$, are
the unique numbers satisfying the moment-cumulant formula

$$m_n = \sum_{\pi \in NC(n)} \prod_{V \in \pi} \kappa_{|V|} \qquad (n \ge 1),$$

the sum running over noncrossing partitions of $\{1, \dots, n\}$. The term of the one-block partition
$1_n$ is $\kappa_n$ and every other partition has blocks of size less than $n$, so the formula is
triangular and is taken as the recursive definition

$$\kappa_n = m_n - \sum_{\pi \in NC(n),\ \pi \ne 1_n} \prod_{V \in \pi} \kappa_{|V|}.$$

For an element $a$ of a noncommutative probability space and $m_n = \varphi(a^n)$, this is the
cumulant $k_n(a) = k_n(a, \dots, a)$ of Anderson, Guionnet and Zeitouni. For example
$\kappa_1 = m_1$ and $\kappa_2 = m_2 - m_1^2$ is the variance. The value at $n = 0$ is $m_0$ and
plays no role.

## Background

- [Noncrossing partitions](../../../Combinatorics/set-partitions/noncrossing-partitions/noncrossing-partitions-and-the-refinement-order/noncrossing-partition.md):
  the index set $NC(n)$ of the moment-cumulant formula.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Definition 5.3.13 (equation (5.3.5)) and Lemma 5.3.14 (the cumulants are
  well defined because the system is triangular).
