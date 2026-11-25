# The free cumulants of the semicircle law

The free cumulants of the standard semicircle law $\sigma$ are $\kappa_2 = 1$ and $\kappa_n = 0$ for
every other $n \ge 1$. In this sense $\sigma$ is the free Gaussian: a classical Gaussian is
characterised by the vanishing of its classical cumulants beyond the second.

Proof: by strong induction on $n$. For $\pi \ne 1_n$, the induction hypothesis turns
$\prod_{V \in \pi} \kappa_{|V|}$ into $1$ if $\pi$ is a pair partition and $0$ otherwise, so
$\sum_{\pi \ne 1_n} \prod_{V} \kappa_{|V|}$ counts the noncrossing pair partitions other than
$1_n$. The moment $\int x^n\,d\sigma$ counts all noncrossing pair partitions of $\{1, \dots, n\}$, so
$\kappa_n$ is $1$ if the one-block partition $1_n$ is a pair partition, that is if $n = 2$, and $0$
otherwise.

## Informally uses

- [The moments of the semicircle law count noncrossing pair partitions](../wigner-s-semicircle-law/integral-pow-semicircle-real-eq-card-non.md):
  the moments in combinatorial form.
- [Free cumulants of a moment sequence](free-cumulant.md): the recursion the induction runs on.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Example 5.3.26 (there obtained from the Stieltjes transform:
  $k_n(a) = 0$ except for $n = 2$, $k_2(a) = \varphi(a^2)$).
