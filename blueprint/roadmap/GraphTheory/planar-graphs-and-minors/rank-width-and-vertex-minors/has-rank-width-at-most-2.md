# Rank-width is at most clique-width (Oum–Seymour)

For every finite graph $G$, $\mathrm{rw}(G) \le \mathrm{cw}(G)$: a graph of clique-width at most $k$ has
rank-width at most $k$. The source's proof reads a rank-decomposition off the parse tree of a
$k$-expression; across each edge of the tree the vertices on one side fall into at most $k$ label
classes with identical neighbourhoods on the other side, so the cut matrix has at most $k$ distinct
rows.

## Background

- [Clique-width is bounded by an exponential in rank-width (Oum–Seymour)](has-clique-width-at-most-2.md):
  the other half of the same proposition.

## Sources

- S. Oum and P. Seymour, *Approximating clique-width and branch-width*, J. Combin. Theory Ser. B 96 (2006) 514–528; read in the authors' preprint of 20 October 2004 (https://sangil.dimag.kr/pdf/rwdfpt.pdf), whose numbering is cited here, Proposition 6.3.
- S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017) 15–24; read as arXiv:1601.03800v2 (27 July 2016), whose numbering is cited here, Theorem 2.1.
