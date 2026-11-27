# Which drift models have the f-statistics of a star tree

Work with the real-valued, square-integrable [drift models](../patterson-s-f-statistics/drift-model.md)
on the same labelled set of $n\ge2$ populations. Their underlying measure spaces may differ.
Call two models f-equivalent when their [f2 matrices](../patterson-s-f-statistics/f2.md)
agree at every pair. This is exact equality, not equality of statistical goodness of fit.
By the [centred-covariance criterion](f2-eq-iff-centred-cov-eq.md), it is equivalent to equality
of their [centred leaf second moments](centred-cov.md), and then all f3 and f4 agree as well.
Centering is across populations at each outcome, not subtraction of each population's
expectation. With $J=I-\mathbf1\mathbf1^{\mathsf T}/n$, lineage-weight matrix $W$ and drift
lengths $\ell$, these centred moments are $K=JW\operatorname{diag}(\ell)W^{\mathsf T}J$;
the common root function cancels under $J$.

Write $D_{ij}=f_2(i,j)$. The model is f-equivalent to a star tree with nonnegative pendant
lengths if and only if there is a vector $s\ge0$ such that

$$D_{ij}=s_i+s_j\qquad(i\ne j).$$

When $n\ge3$ and such a vector exists, it is unique, and for any distinct $i,j,k$,

$$s_i=f_3(i;j,k)=\frac{D_{ij}+D_{ik}-D_{jk}}2.$$

For exactly three populations the three pair equations always have this unique real
solution. Consequently a three-population drift model is star-equivalent if and only if
its three f3 statistics with distinct arguments are nonnegative. For more populations,
nonnegativity alone is not sufficient: the pair equations must also be consistent.
For $n=2$, only $s_1+s_2=D_{12}$ is determined; the nonnegative solutions are
$(a,D_{12}-a)$ with $0\le a\le D_{12}$.

## Depends on

- [f2 statistic](../patterson-s-f-statistics/f2.md)
- [Admixture-graph drift model](../patterson-s-f-statistics/drift-model.md)

## Proof depends on

- [f-statistics determine exactly the centred leaf covariance](f2-eq-iff-centred-cov-eq.md)
- [f2 in the drift model](../patterson-s-f-statistics/f2-freq.md)
- [f3 in terms of f2](../patterson-s-f-statistics/f3-eq-f2.md)
- [f4 in terms of f2](../patterson-s-f-statistics/f4-eq-f2.md)

## Expansion

For necessity, a star has weights $w(i,e)=\mathbf1_{i=e}$, so the drift-model formula gives
$D_{ij}=s_i+s_j$ off the diagonal and $D_{ii}=0$. For sufficiency, choose independent
symmetric signs $\varepsilon_i\in\{-1,1\}$ on a finite probability space, take root zero,
and set the star increments to $\delta_i=\sqrt{s_i}\varepsilon_i$. They are square
integrable, mutually orthogonal, and satisfy $\mathbb E\delta_i^2=s_i$, including zero
lengths. This constructs an actual drift model, on a new space if needed, with the required
f2 matrix. Equality of f3 and f4 follows from their linked f2 identities. This is a
real-valued second-moment realization; no general converse with frequencies constrained
to $[0,1]$ is being asserted.

For three distinct labels, adding the two pair equations through $i$ and subtracting the
third gives the formula for $s_i$, proving uniqueness when $n\ge3$. With exactly three
labels, substituting the three formulas recovers all three pair equations. Thus the
nonnegative-length condition is precisely the three f3 inequalities, or equivalently the
triangle inequalities for $D$ itself, not for its square root.

The [conditionally negative semidefinite](../inner-product-geometry-and-realizability-of-f-st/is-cond-neg-semidef.md)
case is included, not an unresolved assumption. Every square-integrable frequency model
has, for $\sum_i z_i=0$,

$$\sum_{i,j}z_i z_jD_{ij}=-2\int\Bigl(\sum_i z_i p_i\Bigr)^2\,d\mu\le0.$$

More generally, for any symmetric zero-diagonal $3\times3$ matrix the same linear formulas
recover $s$; if $s\ge0$, the star construction realizes it, whether or not conditional
negative semidefiniteness was assumed in advance. In particular this proves the criterion
for a CND f2 matrix. CND alone does not imply nonnegative pendant lengths: squared distances
between the real points $0,1,2$ give $(D_{12},D_{13},D_{23})=(1,4,1)$ and
$s=(2,-1,2)$. Such a matrix is realizable by an unconstrained model but not by a nonnegative
star.

### A four-population tree that is not star-equivalent

For the quartet split $12\mid34$, let the pendant lengths be $b_i\ge0$ and the internal
length be $t\ge0$. Its pair distances are $D_{12}=b_1+b_2$, $D_{34}=b_3+b_4$, and
$D_{ij}=b_i+b_j+t$ across the split. Hence

$$D_{13}+D_{24}-D_{12}-D_{34}=2t.$$

Every star gives zero in this expression. The quartet is therefore star-equivalent exactly
when $t=0$, when $s_i=b_i$ works. For example $b_i=t=1$ gives positive f3 values for every
triple of distinct labels but is not star-equivalent, illustrating why the three-population
criterion cannot be extended using nonnegativity alone.

### A four-population admixture graph that is star-equivalent

Start with a common root. Populations $1,2,3$ have separate private increments $\delta_i$
of lengths $\ell_i$. Two unsampled donor lineages lead from the root to a half-and-half
admixture node, followed by population $4$'s private increment $\delta_4$ of length
$\ell_4$. Let $\eta_1,\eta_2$ be the total increments along the two donor routes, with
second moments $g_1,g_2$. Choose all underlying edge increments independent and centered,
so these two totals and the four private increments are mutually orthogonal. Then
$p_i=r+\delta_i$ for $i\le3$ and
$p_4=r+\delta_4+(\eta_1+\eta_2)/2$.

The increment $\delta'_4=\delta_4+(\eta_1+\eta_2)/2$ is orthogonal to the other three private
increments and has second moment $\ell_4+(g_1+g_2)/4$. Collapsing this unobserved private
history gives a star model with the same four frequency functions and lengths

$$s_i=\ell_i\ (i\le3),\qquad s_4=\ell_4+\frac{g_1+g_2}{4}.$$

Explicitly, each donor route can have a hidden donor node between the root and the admixture
node, with positive drift on both edges. For a concrete bounded example, take root $1/2$
and all eight edge increments independent with values $\pm1/8$: the three private leaf
edges, population $4$'s private edge, and the two edges on each donor route. Every edge has
length $1/64$, each donor route has $g_i=1/32$, and the matching star lengths are
$(1/64,1/64,1/64,1/32)$. All intermediate and leaf frequencies lie in $[0,1]$. The original
graph has a genuine two-parent node and positive drift lengths; the star does not.

The donors in this example are unsampled and affect only population $4$. It establishes
existence of different latent topologies with exactly the same statistics on these four
labels, not star-equivalence of arbitrary admixture graphs or indistinguishability after
adding donor samples.

## Related topics

- [Star tree and admixture model have equal f2](f2-star-eq-f2-admix.md), the existing three-population pair.

## Sources

- R. Maier, P. Flegontov, O. Flegontova, U. Işıldak, P. Changmai and D. Reich,
  "On the limits of fitting complex models of population history to f-statistics",
  eLife 12 (2023), e85492, <https://doi.org/10.7554/eLife.85492>, Introduction, p. 2,
  for the problem of alternative graphs fitting data within statistical resolution.
  The exact algebraic characterization and explicit examples above are derived here;
  they are not attributed to that empirical fitting statement.
