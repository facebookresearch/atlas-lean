# Moriwaki's generalized Hodge index theorem

Let $X$ be a projective arithmetic variety of dimension $d + 1$ in the sense of Moriwaki (an integral
scheme, projective and flat over $\mathbb{Z}$) and $\bar L$ a hermitian line bundle on $X$ such that
$L_\mathbb{Q}$ is nef on $X_\mathbb{Q}$. Say that $L$ has *moderate growth of positive even
cohomologies* if there are a generic resolution of
singularities $\mu \colon Y \to X$ and an ample invertible sheaf $A$ on $Y$ such that for every
integer $n \ge 1$ there is an integer $m_0$ with

$$\log \# H^{2i}\bigl( Y, m(n \mu^* L + A) \bigr) = o(m^{d+1}) \qquad (m \ge m_0,\ i > 0);$$

these groups are finite for $i > 0$ and large $m$, and the estimate is required for each $n$ and all
$i > 0$.

**Theorem** (Moriwaki). Assume that

1. $L_\mathbb{Q}$ is nef on $X_\mathbb{Q}$;
2. the first Chern form $c_1(\bar L)$ is semipositive on $X(\mathbb{C})$;
3. $L$ has moderate growth of positive even cohomologies.

Then $\widehat{\mathrm{vol}}(\bar L) \ge (\bar L^{d+1})$.

**Corollary.** If $L$ is nef on every geometric fibre of $X \to \operatorname{Spec} \mathbb{Z}$ and
$c_1(\bar L)$ is semipositive on $X(\mathbb{C})$, then $\widehat{\mathrm{vol}}(\bar L) \ge
(\bar L^{d+1})$; in particular $\bar L$ is big if $(\bar L^{d+1}) > 0$. Indeed such an $L$ has moderate
growth of positive even cohomologies: for a generic resolution $\mu$ and an ample $A$ on $Y$, every
$n \mu^* L + A$ is ample, so its higher cohomology groups vanish after multiplication by any large
$m$. When $X$ is an arithmetic surface ($d = 1$), condition 3 always holds, so conditions 1 and 2
suffice; the semipositivity of $c_1(\bar L)$ is still needed.

Moriwaki writes $d$ for the absolute dimension of $X$, here $d + 1$; the corollary generalizes
Zhang's theorem on the existence of small sections. Moriwaki first proves the inequality when $X$ is
generically smooth (not necessarily regular), $L_\mathbb{Q}$ is ample, $c_1(\bar L)$ is positive and
$\log \# H^{2i}(X, mL) = o(m^{d+1})$ for $i > 0$ and large $m$ (Claim 6.2.1): the arithmetic
Riemann–Roch theorem in its form for coherent sheaves over $\operatorname{Spec} \mathbb{Z}$, whose
arithmetic Euler characteristic contains the alternating sum of the logarithms of the orders of the
finite higher cohomology groups, and the asymptotics of analytic torsion of Bismut and Vasserot give the
asymptotic expansion of the $L^2$ Euler characteristic of $H^0(X, mL)$ corrected by these orders; his
Proposition 2.1 (1) and (3) on normed lattices and Gromov's inequality pass from it to the number of
small sections for the sup norm. In general he applies this to $n \mu^* L + A$, divides the resulting
inequality by $n^{d+1}$ using homogeneity (the class being scaled by $1/n$), lets $n \to \infty$ by the
continuity of the volume, and returns to $X$ by birational invariance and the projection formula for
arithmetic intersection numbers.

## Depends on

- [Arithmetic varieties and hermitian vector bundles](../arithmetic-variety.md), for projective arithmetic varieties and generic resolutions of singularities
- [Positivity of hermitian line bundles](../positivity-of-hermitian-line-bundles.md), for semipositivity and bigness
- [Arithmetic volume](arithmetic-volume.md)
- [Arithmetic degree and arithmetic intersection numbers](../arithmetic-intersection-numbers.md), for $(\bar L^{d+1})$
- [Nef and big line bundles](../../birational-geometry/nef-and-big-line-bundles.md), for nef line bundles on $X_\mathbb{Q}$ and on the geometric fibres

## Proof depends on

- [Arithmetic Riemann–Roch theorem](../arithmetic-riemann-roch-theorem.md), in its form (14)–(15) for hermitian coherent sheaves over $\operatorname{Spec} \mathbb{Z}$, in the generically smooth case (Claim 6.2.1)
- [Small elements of normed lattices](../small-elements-of-normed-lattices.md), for Moriwaki's Proposition 2.1 (1) and (3) (Claim 6.2.1)
- [Gromov's inequality](../gromov-inequality.md), for the comparison of $L^2$ and sup norms (Claim 6.2.1)
- [Analytic torsion and Quillen metrics](../analytic-torsion-and-quillen-metrics.md), for the asymptotics of analytic torsion of Bismut and Vasserot (Claim 6.2.1)
- [Continuity of the arithmetic volume](continuity-of-the-arithmetic-volume.md)
- [Arithmetic volume](arithmetic-volume.md), for homogeneity (Proposition 4.7) and birational invariance (Theorem 4.2)
- [Arithmetic degree and arithmetic intersection numbers](../arithmetic-intersection-numbers.md), for the projection formula
- [Resolution of singularities of quasi-projective varieties](../../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md), for the generic resolution of singularities

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Theorem B and the
  paragraph after it, p. 2; Section 6, the definition of moderate growth of positive even
  cohomologies and Example 6.1 (1)–(2), p. 40, Theorem 6.2 (generalized Hodge index theorem) with
  its proof and Claim 6.2.1, pp. 40–41, Corollaries 6.3 and 6.4, pp. 41–42; Proposition 2.1, p. 13.
- J.-M. Bismut and E. Vasserot, "The asymptotics of the Ray–Singer analytic torsion associated with
  high powers of a positive line bundle", Comm. Math. Phys. 125 (1989), 355–367, as cited by
  Moriwaki.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses the corollary, for hermitian line bundles nef on the fibres with semipositive curvature, as `GlobalTheory.Published.VolGe`.
