# Rank-width is at most tree-width plus one

A finite graph of tree-width at most $k$ has rank-width at most $k + 1$. The converse fails:
complete graphs have rank-width at most one but unbounded tree-width.

The derivation has two steps.

1. $\mathrm{rw}(G) \le \mathrm{bw}(G)$ unless $\mathrm{bw}(G) = 0$. The survey derives this from a
   theorem of Oum: if $G$ has branch-width $k \ne 0$, its incidence graph has rank-width $k$ or
   $k - 1$, and $G$ is a vertex-minor of its incidence graph.
2. $\mathrm{bw}(G) \le \mathrm{tw}(G) + 1$, a theorem of Robertson and Seymour (*Graph Minors. X.
   Obstructions to tree-decomposition*, J. Combin. Theory Ser. B, 1991; not consulted here). The
   survey states the conclusion $\mathrm{rw}(G) \le \mathrm{tw}(G) + 1$ without spelling out this
   step. When $\mathrm{bw}(G) = 0$, step 1 does not apply and the bound is checked separately.

## Informally uses

- [Rank-width does not increase under vertex-minors](has-rank-width-at-most-3.md): $G$ is a
  vertex-minor of its incidence graph.

## Background

- [Tree-width at most k](../tree-width/has-treewidth-at-most.md) and
  [complete graphs have cut-rank at most one](cut-rank-top-le-one.md).

## Sources

- S. Oum, *Rank-width: algorithmic and structural results*, Discrete Appl. Math. 231 (2017) 15–24; read as arXiv:1601.03800v2 (27 July 2016), whose numbering is cited here, Section 4.2 and Theorem 4.1, citing S. Oum, *Rank-width is less than or equal to
  branch-width*, J. Graph Theory, 2008 (not consulted here).
