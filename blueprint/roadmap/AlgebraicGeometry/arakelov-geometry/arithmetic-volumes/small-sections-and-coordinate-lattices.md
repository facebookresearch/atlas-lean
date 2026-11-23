# Small sections and lattices of homogeneous coordinate rings

This node is still to be broken down. It covers the comparison between small sections of powers of a
hermitian line bundle on a projective arithmetic variety and small elements of lattices of functions
attached to a coordinate presentation of the variety, which turns the arithmetic Hilbert–Samuel
formula for nef hermitian line bundles and Moriwaki's lower bound for the arithmetic volume into
bounds for counts of small elements of these lattices. The four targets below are the forms used by
Alpöge's library; no published source states them, and they are recorded here as unsourced targets.

**Setting.** Let $\Omega$ be a field and $y = (y_{k,i})$ a finite family of elements of $\Omega$, in
blocks $k \in K$. The kernel $P$ of $x_{k,i} \mapsto y_{k,i} T_k$, from the multigraded polynomial
ring over $\mathbb{Z}$ to $\Omega[T_k]_{k \in K}$, is a multihomogeneous prime ideal defining an
integral closed subscheme $X$ of $\prod_k \mathbb{P}^{|\iota(k)| - 1}_\mathbb{Z}$, assumed flat over
$\mathbb{Z}$ of dimension $D + 1$; the presentation is *birational* if every element of $\Omega$ is
a ratio $g(y) / h(y)$ of multihomogeneous polynomials of the same multidegree. A chart is a choice
$c(k) \in \iota(k)$ with all $y_{k,c(k)} \ne 0$, with chart ring $\mathbb{Z}[y_{k,i} / y_{k,c(k)}]
\subset \Omega$. Let $\bar A$ be a hermitian line bundle on the ambient product, of multidegree $a
\in \mathbb{Z}^K$, with metric $h_A$. For $\tau \ge 0$ there are three different groups of elements
of multidegree $\tau a$:

- `secM`: the $\mathbb{Z}$-span of the values $g(y)$ of integral multihomogeneous polynomials $g$ of
  multidegree $\tau a$, defined only for $a \ge 0$ (there is no polynomial of negative degree);
- `chartLat`: the $s \in \Omega$ such that $s \prod_k y_{k,c(k)}^{-\tau a_k}$ lies in the chart ring
  for every chart $c$;
- `chartLatNm`: the same with the integral closure of each chart ring in $\Omega$.

An element $s$ is *small* if $|g(z)| \le |h(z)|\, h_A(z)^\tau$ at every complex point $z$ of the
cone over $X$, for all integral multihomogeneous $g$, $h$ with $\deg g = \deg h + \tau a$ and $g(y)
= s\, h(y)$; pairs with $h(y) = 0$ are allowed, and then $g$ and $h$ both lie in $P$ and vanish on
the cone. $N_\tau$ denotes the number of small elements of a group in degree $\tau$, finite since
they are lattice points of bounded sup norm. The second and third groups differ, and no bounded
index relates them in general: for the cuspidal cubic $y^2 z = x^3$ the chart ring on $z = 1$ is
$\mathbb{Z}[t^2, t^3]$, with integral closure $\mathbb{Z}[t]$; the normalization $\mathbb{P}^1 \to
X$, $[u : v] \mapsto [u^2 v : u^3 : v^3]$, pulls $\mathcal{O}(1)$ back to $\mathcal{O}(3)$, whose
sections of degree $3n$ have dimension $3n + 1$, while the products of $u^2 v$, $u^3$ and $v^3$ span
a space of dimension $3n$.

**Intersection numbers and relative semipositivity.** In all four targets $(\bar A^{D+1} \cdot X)$
is the value at $(P, D + 1, \bar A)$ of an arbitrary *intersection system*: a function of a
multihomogeneous prime ideal, a dimension and a tuple of hermitian line bundles on the ambient
product that is symmetric and additive in smooth metrics and satisfies, for every multihomogeneous
form $s \notin P$ of the degree of the last bundle, the recursion of the
[arithmetic Poincaré–Lelong formula](../poincare-lelong-formula-on-arithmetic-cycles.md): the sum
over the relevant minimal primes $W$ of $P + (s)$ of their multiplicities times the value at $W$
(for horizontal $W$) or the geometric degree times $\log p$ (for $W$ over $p$), minus the
archimedean integral of $\log(|s| / h_A)$ (the library's `IsIntersectionSystem`). The targets hold
for every such system. *Relatively semipositive* means, here, for an auxiliary multihomogeneous
ideal $P_0 \subseteq P$ (the ideal of an ambient variety containing $X$): $h_A$ is smooth, and at
every complex point of the cone over $X$ the Levi form of $\log h_A$ is nonnegative in every
direction tangent to the cone of $P_0$ (`IsSemipositiveRel`). This is an archimedean condition, not
the relative semipositivity of
[positive hermitian line bundles](../positivity-of-hermitian-line-bundles.md), which also involves
the degrees on the closed fibres; those are separate hypotheses below.

The targets are:

1. (Nonnegativity.) For an arbitrary horizontal multihomogeneous prime $P$ defining $X$ of dimension
   $D + 1$, not necessarily a coordinate ideal: if $\bar A$ is relatively semipositive, invariant
   under complex conjugation, nef on the fibres over the closed points of $\operatorname{Spec}
   \mathbb{Z}$ and of nonnegative degree on every horizontal curve of $X$, then $(\bar A^{D+1} \cdot
   X) \ge 0$, for any multidegree $a$.
2. (Upper bound on `chartLat`.) If $D \ge 1$, $\Omega$ has characteristic zero, the presentation is
   birational, $\bar A$ is invariant under conjugation and has a small generating datum (it is
   relatively semipositive, its generic degree is positive, and finitely many small elements $w_j$
   of the group `chartLat` in degree $1$ have trivializations $w_j \prod_k y_{k,c(k)}^{-a_k}$ that
   generate the unit ideal of every chart ring), then $\limsup_\tau \log N_\tau /
   (\tau^{D+1}/(D+1)!) \le (\bar A^{D+1} \cdot X)$, where $N_\tau$ is the number of small elements
   of `chartLat` in degree $\tau$.
3. (Upper bound on `chartLatNm`.) If $D \ge 1$, the presentation is birational, $a$ is entrywise
   nonnegative, $\bar A$ is relatively semipositive and invariant under conjugation, and every
   monomial of multidegree $a$ is bounded by $h_A$ on the cone over $X(\mathbb{C})$
   (`MonomialsBounded`), the same bound holds with $N_\tau$ the number of small elements of
   `chartLatNm`.
4. (Lower bound on `chartLat`.) If the presentation is birational and $\bar A$ is relatively
   semipositive, invariant under conjugation, and nef on the generic fibre and on the closed fibres,
   then $(\bar A^{D+1} \cdot X)$ is at most the arithmetic volume $\limsup_\tau \log N_\tau /
   (\tau^{D+1}/(D+1)!)$ computed with the small elements of `chartLat`, a count of lattice points,
   not a covolume.

The diagonal case of a hermitian $\mathcal{O}(1, \dots, 1)$ is a special case of all four. A good
expansion has pages for: the restriction from integral polynomials of multidegree $\tau a$ to
sections of $L^{\otimes \tau}$ on $X$, surjective for large $\tau$ by Serre vanishing for the ideal
of $X$ when **every** $a_k \ge 1$, the ambient bundle being then ample (the library's comparison
`chartLat` = `secM` in large degree assumes the same); for weights that are merely nonnegative it
can fail in every degree: for $X \cong \mathbb{P}^1_\mathbb{Z}$ embedded in $\mathbb{P}^1 \times
\mathbb{P}^1$ as the graph of $[u : v] \mapsto [u^2 : v^2]$ and $a = (1, 0)$, which restricts to
$\mathcal{O}(2)$, the restrictions of the polynomials of bidegree $(\tau, 0)$ span $\tau + 1$
dimensions on the generic fibre while $h^0(\mathcal{O}(2\tau)) = 2\tau + 1$, and for nonnegative or
signed weights the targets need instead a twisted comparison of `chartLat` and `chartLatNm` with
sections on $X$; separately, the comparison of the three groups with these sections, including the
contribution of the normalization, at the scale $o(\tau^{D+1})$ needed here; the comparison of the
norms defining smallness with sup norms of sections, by
[Gromov's inequality](../gromov-inequality.md) and the estimates for
[normed lattices](../small-elements-of-normed-lattices.md); and the deduction of 1–3 from the
[nef Hilbert–Samuel formula](arithmetic-hilbert-samuel-formula-for-nef-hermitian-line-bundles.md)
and of 4 from [Moriwaki's generalized Hodge index theorem](generalized-hodge-index-theorem.md). Over
the ring of integers of a number field, integrality over $\mathbb{Z}$ and over that ring are to be
distinguished.

## Depends on

- [Arithmetic varieties and hermitian vector bundles](../arithmetic-variety.md)
- [Positivity of hermitian line bundles](../positivity-of-hermitian-line-bundles.md)
- [Arithmetic degree and arithmetic intersection numbers](../arithmetic-intersection-numbers.md)
- [Poincaré–Lelong formula on arithmetic cycles](../poincare-lelong-formula-on-arithmetic-cycles.md),
  for the recursion defining intersection systems
## Proof depends on

- [Arithmetic Hilbert–Samuel formula for nef hermitian line bundles](arithmetic-hilbert-samuel-formula-for-nef-hermitian-line-bundles.md)
- [Moriwaki's generalized Hodge index theorem](generalized-hodge-index-theorem.md)
- [Gromov's inequality](../gromov-inequality.md)
- [Small elements of normed lattices](../small-elements-of-normed-lattices.md)

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Theorem A and
  Theorem B, p. 2; Corollary 5.5, pp. 38–39; Corollary 6.4, p. 42.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  states 1 as `GroundTheory.Heights₂.Heights.HilbertSamuel.ArithKleiman.Statement`, for an
  axiomatized intersection system, 2 as `GroundTheory.Heights₂.Heights.HilbertSamuel.G7.Statement`,
  3 as `ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticHilbertSamuelUpperBound` (the three
  combined as `PositivityTheory.MbHsUse.HSUse`), and 4 as
  `ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement`, with the groups
  `secM`, `chartLat` and `chartLatNm`, the smallness predicate `IsSmallH` and the volume `arVolP`
  above.
