# Excluded vertex-minors for bounded rank-width (Oum)

Let $k \ge 1$. A finite graph $G$ has rank-width at most $k$ if and only if every vertex-minor of $G$
with at most $(6^{k+1} - 1)/5$ vertices has rank-width at most $k$.

The source states its main theorem as: the set of graphs of rank-width at most $k$ is characterised
by excluded vertex-minors with at most $(6^{k+1} - 1)/5$ vertices. The statement here is
equivalent: one direction is monotonicity under vertex-minors, and conversely a graph of rank-width
greater than $k$ contains a vertex-minor of rank-width greater than $k$ with as few vertices as
possible; all its proper pivot-minors (which are vertex-minors) have rank-width at most $k$, so
by Theorem 5.4 it has at most $(6^{k+1} - 1)/5$ vertices. In particular, for each $k$ there are finitely many excluded
vertex-minors. For $k = 1$ the source shows that the graphs of rank-width at most one are exactly
the distance-hereditary graphs.

## Background

- [Rank-width does not increase under vertex-minors](has-rank-width-at-most-3.md): the easy
  direction.

## Sources

- S. Oum, *Rank-width and vertex-minors*, J. Combin. Theory Ser. B 95 (2005) 79–100; read in the author's revised preprint of 18 April 2005 (https://sangil.dimag.kr/pdf/vertexminor-revision.pdf), whose numbering is cited here, Theorem 5.4 and Corollary 5.5 (the main theorem, stated in Section 1); Section 7 for $k = 1$.
- S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017) 15–24; read as arXiv:1601.03800v2 (27 July 2016), whose numbering is cited here, Section 4.7.
