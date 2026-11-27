# Farthest-first traversal sketching of single-cell data

**Sketching problem.** Let $X$ be a finite set of cells (points in a metric space $(M, d)$, e.g.
expression profiles with the Euclidean metric). A sketch is a subset $S \subseteq X$ of size $k$, and
its quality is the Hausdorff distance

$$d_H(X, S) = \max_{x \in X} \min_{s \in S} d(x, s),$$

the largest distance from any cell to its nearest representative. Minimizing it over $|S| = k$ is the
metric $k$-center problem, with optimum $d_H^{\mathrm{opt}}(X, k)$.

**Farthest-first traversal.** Start from an arbitrary point $x_1 \in X$ and repeatedly add the point
least well represented so far,

$$x_{\ell+1} = \operatorname*{arg\,max}_{x \in X}\ \min_{1 \le j \le \ell} d(x, x_j).$$

**Theorem (2-approximation).** For every $k$, the first $k$ points $S_k = \{x_1, \dots, x_k\}$ of a
farthest-first traversal satisfy

$$d_H(X, S_k) \le 2\, d_H^{\mathrm{opt}}(X, k).$$

**Theorem (hardness).** For any $\alpha < 2$, unless $\mathrm{P} = \mathrm{NP}$ no polynomial-time
algorithm guarantees, on all finite metric spaces, $d_H(X, S) \le \alpha\, d_H^{\mathrm{opt}}(X, k)$.

**Pruning by the triangle inequality.** When a new point $p$ is added at distance $r$ from its
nearest previous representative:

1. a point $x$ can switch its nearest representative from $s$ to $p$ only if $d(s, x) \ge r/2$;
2. if $d(s, p) \ge 2r$, no point currently assigned to $s$ needs updating.

## Depends on

- [The k-center objective](../../../../ComputerScience/approximation-algorithms/metric-k-center-steiner-tree-and-tsp/k-center-objective.md)

## Proof depends on

- [Gonzalez's farthest-first traversal is a 2-approximation for metric k-center](../../../../ComputerScience/approximation-algorithms/metric-k-center-steiner-tree-and-tsp/gonzalez-farthest-first-two-approximation.md)
- [Approximating metric k-center within a factor below 2 is NP-hard](../../../../ComputerScience/approximation-algorithms/metric-k-center-steiner-tree-and-tsp/k-center-hardness-below-two.md)

## Expansion

For the approximation bound, let $r = d_H(X, S_k)$, attained at the point $x_{k+1}$ the traversal
would choose next. The $k + 1$ points $x_1, \dots, x_{k+1}$ are pairwise at distance at least $r$,
because each was the farthest from its predecessors at a time when the covering radius was at least
$r$. Any $k$ centres must place two of them in the same optimal cluster, whose diameter is at most
$2 d_H^{\mathrm{opt}}$, so $r \le 2 d_H^{\mathrm{opt}}$. The traversal is nested: every prefix of
length $\ell$ is itself within a factor two of optimal for size $\ell$, so one ordering serves every
sketch size. For pruning rule 1, $r \le d(s, p) \le d(s, x) + d(x, p)$, and switching requires
$d(x, p) \le d(s, x)$, hence $d(s, x) \ge r/2$; for rule 2, $d(x, p) \ge d(s, p) - d(s, x) \ge 2r - r \ge d(s, x)$,
since every point is within the current covering radius $r$ of its representative. Compared with uniform subsampling, a minimax-distance sketch retains rare cell
types, because a small distant cluster is exactly where the covering radius is largest.

## Sources

- B. DeMeo, B. Berger, "Hopper: a mathematically optimal algorithm for sketching biological data",
  Bioinformatics 36 (Suppl 1) (2020) i236-i241, Section 2.1, Eq. (1), Theorems 1-2 and the geometric
  speedups, <https://doi.org/10.1093/bioinformatics/btaa408> (PMC7355272).
- T. F. Gonzalez, "Clustering to minimize the maximum intercluster distance", Theoretical Computer
  Science 38 (1985) 293-306, <https://doi.org/10.1016/0304-3975(85)90224-5>.
