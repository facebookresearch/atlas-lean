# Scaling to prescribed row and column sums

Let $A$ be a real $n \times m$ matrix with nonnegative entries, $n, m \ge 1$, and let $r \in \mathbb{R}^n$ and
$c \in \mathbb{R}^m$ have positive entries. The following are equivalent:

1. there are diagonal matrices $D_1$, $D_2$ with positive diagonal entries such that $D_1 A D_2$ has row sums $r$ and
   column sums $c$;
2. there is a real $n \times m$ matrix $B \ge 0$ with $B_{ij} > 0$ exactly when $A_{ij} > 0$ that has row sums $r$ and
   column sums $c$;
3. the alternating scaling iteration, which starts from $A$ and repeatedly rescales the rows to sums $r$ and then the
   columns to sums $c$, is defined at every step, converges, and the products of its row factors and of its column
   factors converge to diagonal matrices with positive diagonal entries. Convergence of the scaled matrices alone is not
   enough: the iterates of $\begin{pmatrix}1&1\\0&1\end{pmatrix}$ with unit margins converge to the identity, which has
   lost an entry of the support.

In that case $\sum_i r_i = \sum_j c_j$. The square case with positive entries and unit margins is Sinkhorn's scaling
theorem; here the matrix may be rectangular, may have zero entries, and the margins need not be uniform.

## Depends on

## Proof depends on

## Sources

- M. Idel, *A review of matrix scaling and Sinkhorn's normal form for matrices and positive maps*, arXiv:1609.06349v1, 2016, Theorem 4.1, items 1, 2 and 5 (p. 24), which attributes them to Menon (1968), Brualdi (1968) and Sinkhorn and Knopp (1967), <https://arxiv.org/abs/1609.06349>.
