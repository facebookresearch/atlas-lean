# Reciprocal sign epistasis, multiple peaks and the small-face limitation

Let $L\ge1$ be an integer and $f:\{0,1\}^L\to\mathbb R$ have distinct
values. Neighbors differ at one locus; a peak exceeds all its neighbors.
For a two-dimensional face based at $g$, put
$a=f(g)$, $b=f(g^i)$, $c=f(g^j)$ and $d=f(g^{ij})$, where $i\ne j$ and
superscripts toggle coordinates. The interaction contrast is
$\epsilon=d-b-c+a$. Call $\epsilon\ne0$ without either sign reversal pure
magnitude epistasis. Sign reversal for locus $i$ means
$(b-a)(d-c)<0$; for locus $j$ it means $(c-a)(d-b)<0$.
Reciprocal sign epistasis means both inequalities.

1. On a full two-locus square, reciprocal sign epistasis is equivalent to
   two peaks, necessarily at opposite corners.
2. In any dimension, two or more peaks imply reciprocal sign epistasis on
   some two-dimensional face.
3. Reciprocal sign epistasis on a face does not imply multiple peaks of a
   higher-dimensional landscape. For a three-cube with coordinates $(x,y,z)$,
   use
   $f(000)=3,f(100)=0,f(010)=1,f(110)=2$ and
   $f(001)=4,f(101)=5,f(011)=6,f(111)=7$.
   The $z=0$ face has reciprocal sign epistasis, but $111$ is the only peak
   of the full cube. The example extends to every $L>3$ by adding the
   positive term $8\sum_{j=4}^L2^{j-4}x_j$.

## Expansion

The square equivalence follows by comparing the two edge effects for each
coordinate: with a scalar fitness and no ties, both reversals force one
opposite pair to exceed the other pair. For necessity in any dimension,
choose a simple path between two distinct peaks whose minimum fitness is
as large as possible. Its unique minimum $w$ is an interior vertex, since
each endpoint is a peak. The two path neighbors of $w$ are distinct and
have higher fitness. They differ from $w$ at different coordinates and
have a second common neighbor $z$ on their square. If $f(z)>f(w)$,
replace the two-edge segment through $w$ by that through $z$, removing loops
if necessary. This gives a path with strictly larger minimum, a
contradiction. Distinctness implies $f(z)<f(w)$, so the two path neighbors
are opposite peaks of that square and give reciprocal sign epistasis.

In the three-cube example all vertical edges increase fitness, and the
upper face has only the peak $111$. This proves the stated limitation of
one face, not the blanket claim that no local condition can ever suffice.
Ties, neutral plateaus and other notions of neighborhood need separate
formulations.

## Sources

- F. J. Poelwijk, S. Tănase-Nicola, D. J. Kiviet and S. J. Tans, "Reciprocal sign epistasis is a necessary condition for multi-peaked fitness landscapes", Journal of Theoretical Biology 272 (2011), 141–144, <https://doi.org/10.1016/j.jtbi.2010.12.015>, abstract (the necessity result). The finite-graph proof and the precise non-sufficiency example are supplied above; the paper's broader Morse-theoretic claim is not invoked.
