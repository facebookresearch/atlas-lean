# Moriwaki's estimate for small sections along an ample divisor

Let $X$ be a projective arithmetic variety in the sense of Moriwaki, generically smooth, of absolute
dimension $D \ge 2$, and let $\bar L$ and $\bar A$ be hermitian line bundles on $X$, written
additively. Assume:

1. $A$ and $L + A$ are very ample over $\mathbb{Q}$;
2. the first Chern forms $c_1(\bar A)$ and $c_1(\bar L + \bar A)$ are positive on $X(\mathbb{C})$;
3. there is a nonzero section $s \in H^0(X, A)$ such that the vertical component of
   $\operatorname{div}(s)$ is contained in the regular locus of $X$ and the horizontal component of
   $\operatorname{div}(s)$ is smooth over $\mathbb{Q}$.

Then there are positive constants $a_0$, $C$ and $C'$, depending only on $X$, $\bar L$ and $\bar A$,
such that for all integers $a \ge b \ge c \ge 0$ with $a \ge a_0$

$$\hat h^0\bigl( a \bar L + (b - c) \bar A \bigr) \le \hat h^0\bigl( a \bar L - c \bar A \bigr) +
C b a^{D-1} + C' a^{D-1} \log a,$$

where $\hat h^0(\bar M) = \log \#\{ t \in H^0(X, M) : \lVert t \rVert_{\sup} \le 1 \}$; the same
holds, with other constants, for the $L^2$ norms defined by the volume form $\Omega(\bar L + \bar
A)$ of Moriwaki's Conventions and terminology 5. For $D = 1$ Moriwaki proves the analogous estimate,
with error $C b + C'$ for all integers $a, b, c \ge 0$, over an integral domain $R$ finite and flat
over $\mathbb{Z}$ whose fraction field is a number field, for free $R$-modules of rank one normed at
the embeddings of that field, the sup norm being the maximum over the embeddings, provided $\bar A$
has a nonzero element of norm at most $1$ (Proposition 3.5); for invertible modules over the maximal
order that are not free one passes to tensor powers. If $X$ is generically smooth of dimension $D
\ge 2$ and $\bar A$ is ample, then for every hermitian line bundle $\bar L$ the hermitian line
bundle $n \bar A$ satisfies 1–3 for all large $n$ (Lemma 3.6).

Moriwaki calls this estimate the technical core of his proof of the continuity of the arithmetic
volume. Its proof uses the estimates for normed lattices of his Proposition 2.1, Gromov's
inequality, the bounds of his Lemma 3.1 for the numbers of small sections, which rest on the
arithmetic Hilbert–Samuel theorem and Zhang's ampleness theorem, and analytic estimates of his §1
that Gromov's inequality does not give: Corollary 1.2.2 (pp. 11–12), a consequence of the distortion
estimate Theorem 1.2.1, in Claim 3.4.3; Lemma 1.1.4, which bounds the $L^2$ norm on $X(\mathbb{C})$
by the $L^2$ norm on an open set meeting every component, and Corollary 1.1.3, on restriction to a
smooth submanifold, in Claim 3.4.4; and the sub- and quotient norms on thickened divisors of Claim
3.4.5 (pp. 21–24). Lemma 3.6 uses an arithmetic Bertini argument or the paper's construction by
Serre vanishing.

## Depends on

- [Arithmetic varieties and hermitian vector bundles](../arithmetic-variety.md), for projective and
  generically smooth arithmetic varieties and the sup norm

## Proof depends on

- [Small elements of normed lattices](../small-elements-of-normed-lattices.md), for Moriwaki's
  Proposition 2.1
- [Gromov's inequality](../gromov-inequality.md)
- [Arithmetic Hilbert–Samuel theorem](../arithmetic-hilbert-samuel-theorem.md), through Moriwaki's
  Lemma 3.1
- [Zhang's arithmetic ampleness theorem](../arithmetic-ampleness-theorem.md), through Moriwaki's Lemma 3.1
- [Estimates for small sections along an effective divisor](estimates-for-small-sections-along-a-divisor.md),
  for the distortion and restriction estimates of Moriwaki's §1
- [Standard results of coherent cohomology on projective varieties](../../birational-geometry/standard-results-of-coherent-cohomology.md),
  for Serre vanishing on $X$, projective over $\mathbb{Z}$ (item 2), which in Moriwaki's Lemma 3.6
  makes $H^0(X, n A)$ surject onto the fibres of $nA$ at finitely many closed points of vertical
  fibres, and for flat base change along $\mathbb{Z} \to \mathbb{Q}$ (item 2)

## Sources

- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Theorem C of the
  introduction, p. 2; Corollary 1.1.3, Lemma 1.1.4, Theorem 1.2.1 and Corollary 1.2.2, pp. 8–12;
  Lemma 3.1, pp. 15–16; Theorem 3.4 (both the $L^2$ and the sup version) with its proof, pp. 19–25,
  Claims 3.4.3–3.4.5, pp. 21–24; Proposition 3.5, p. 25; Lemma 3.6 with its proof, p. 26 (for $D \ge
  2$).
