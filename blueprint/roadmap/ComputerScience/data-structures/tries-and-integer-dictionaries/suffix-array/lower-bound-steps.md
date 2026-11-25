# Number of probes made by the binary search

Let $p$ be a test on natural numbers and $lo, hi \in \mathbb{N}$. The number of probes
$\nu(p, lo, hi)$ of the binary search is defined by recursion on $hi - lo$: if $lo < hi$, let
$m = \lfloor (lo + hi)/2 \rfloor$; then $\nu(p, lo, hi) = \nu(p, m + 1, hi) + 1$ if $p(m)$ is true
and $\nu(p, lo, hi) = \nu(p, lo, m) + 1$ otherwise. If $lo \ge hi$, then $\nu(p, lo, hi) = 0$.
