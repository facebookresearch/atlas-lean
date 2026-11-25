# Clique-width is bounded by an exponential in rank-width (Oum–Seymour)

For every finite graph $G$, $\mathrm{cw}(G) \le 2^{\mathrm{rw}(G) + 1} - 1$: a graph of rank-width at most
$k$ has clique-width at most $2^{k+1} - 1$. With the inequality $\mathrm{rw}(G) \le \mathrm{cw}(G)$, a
class of graphs has bounded rank-width if and only if it has bounded clique-width. The source's
proof builds a $(2^{k+1} - 1)$-expression bottom-up along a rooted rank-decomposition, using that
a matrix of rank at most $k$ over $\mathrm{GF}(2)$ has at most $2^k - 1$ distinct nonzero rows.

The bounds are essentially tight: the $n \times n$ grid has rank-width $n - 1$ and clique-width
$n + 1$, and there are graphs of rank-width at most $k + 1$ and clique-width at least
$2^{\lfloor k/2 \rfloor - 1}$ (survey, after Theorem 2.1).

## Background

- [Rank-width is at most clique-width (Oum–Seymour)](has-rank-width-at-most-2.md): the other half
  of the same proposition.

## Sources

- S. Oum and P. Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory Ser. B 96 (2006) 514–528; read in the authors' preprint of 20 October 2004 (https://sangil.dimag.kr/pdf/rwdfpt.pdf), whose numbering is cited here, Proposition 6.3.
- S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017) 15–24; read as arXiv:1601.03800v2 (27 July 2016), whose numbering is cited here, Theorem 2.1.
