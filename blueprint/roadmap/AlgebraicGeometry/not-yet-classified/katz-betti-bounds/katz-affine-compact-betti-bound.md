# Katz's bound on the compact Betti numbers of an affine scheme

Let $k$ be an algebraically
closed field, $N > 1$ and $r > 0$ integers, $F_1, \dots, F_r \in k[x_1, \dots, x_N]$ polynomials of
total degree at most $d$, $\ell$ a prime invertible in $k$, and $c$ a chosen compactification of the
affine scheme $V = \operatorname{Spec} k[x_1, \dots, x_N]/(F_1, \dots, F_r)$. Then the compactly
supported $\ell$-adic cohomology groups $H^n_c(V, \mathbb{Q}_\ell)$ computed in $c$
(`CompactAdicCohomology ell c n`) are finite-dimensional over $\mathbb{Q}_\ell$ for every $n$, and
the sum of their dimensions over any finite set of degrees is at most `katzBound N r d`
$= 6 \cdot 2^r (3 + r d)^{N + 1}$.
