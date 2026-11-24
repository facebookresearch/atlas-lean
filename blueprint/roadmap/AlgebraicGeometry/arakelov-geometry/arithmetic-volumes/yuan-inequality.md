# Yuan's inequality for arithmetic volumes

Let $X$ be an arithmetic variety of dimension $d + 1$ in the sense of Zhang (an integral scheme,
projective and flat over $\mathbb{Z}$), and let $\bar L$, $\bar M$ and $\bar E$ be hermitian line
bundles on $X$, written additively. If $\bar L$ and $\bar M$ are ample in Zhang's sense, then

$$\chi_{\sup}\bigl( \bar E + N(\bar L - \bar M) \bigr) \ge \frac{(\bar L^{d+1}) - (d + 1)
(\bar L^d \cdot \bar M)}{(d + 1)!} \, N^{d+1} + o(N^{d+1}) \qquad (N \to \infty),$$

meaning that the difference of the two sides is bounded below by a function that is $o(N^{d+1})$;
here $(\bar L^d \cdot \bar M)$ is the arithmetic intersection number of $d$ copies of $\bar L$ and
one of $\bar M$. In particular $\bar L - \bar M$ is strongly big if $(\bar L^{d+1}) > (d + 1)(\bar
L^d \cdot \bar M)$.

Moriwaki extends the consequence for volumes to nef hermitian $\mathbb{Q}$-line bundles: if $X$ is a
projective arithmetic variety of dimension $d + 1$ and $\bar L$, $\bar M$ are nef hermitian
$\mathbb{Q}$-line bundles on $X$, then

$$\widehat{\mathrm{vol}}(\bar L - \bar M) \ge (\bar L^{d+1}) - (d + 1)(\bar L^d \cdot \bar M).$$

For $\bar L$ and $\bar M$ ample in Moriwaki's sense this follows from Yuan's inequality, since the
logarithm of the number of small sections is bounded below by $\chi_{\sup}$ up to a term linear in
the rank (Moriwaki's Proposition 2.1 (1)), and by homogeneity it holds for ample hermitian
$\mathbb{Q}$-line bundles. For nef $\bar L$ and $\bar M$ and an ample $\bar A$, $\bar L +
\varepsilon \bar A$ and $\bar M + \varepsilon \bar A$ are ample for rational $\varepsilon > 0$
(Moriwaki, proof of Theorem 5.6) and $\widehat{\mathrm{vol}}(\bar L - \bar M) =
\widehat{\mathrm{vol}}((\bar L + \varepsilon \bar A) - (\bar M + \varepsilon \bar A))$; the
right-hand side of the ample case is a polynomial in $\varepsilon$, and letting $\varepsilon \to 0$
gives the inequality. This argument does not use the continuity of the volume. Moriwaki writes $d$
for the absolute dimension of $X$, here $d + 1$, and Yuan writes $n$.

Yuan reduces his theorem to the case where $X$ is normal and generically smooth, using a generic
resolution and the comparison of $\chi_{\sup}$ under birational morphisms (Proposition 2.8), to the
case where $\bar L$ and $\bar M$ have positive curvature, by perturbing with $\varepsilon \bar H$
for an ample $\bar H$ (Lemma 2.9), and to the case where $\bar M$ has a strictly effective section,
of sup norm less than $1$, whose divisor has Cartier components, using Moriwaki's small-section
Bertini theorem. He then follows Abbes and Bouche's proof of the arithmetic Hilbert–Samuel theorem,
comparing $L^2$ volumes along the multiplication by that section with the help of distortion
functions and Gromov's inequality (his Theorems 2.10–2.11, Propositions 2.12–2.14 and Lemmas
2.15–2.16, with the classical Hilbert–Samuel formula on the vertical components of the divisor and
the arithmetic one on its horizontal components), and concludes with the arithmetic Hilbert–Samuel
formula for $\chi_{L^2}(\bar E + N\bar L)$. Proposition 2.8, a one-sided comparison of $\chi_{\sup}$
under birational morphisms at leading order ($\chi$ downstairs is at least $\chi$ upstairs up to
$o(N^n)$), itself uses the arithmetic Hilbert–Samuel formula and the existence of bases of small
sections for ample hermitian line bundles (Corollary 2.7).

## Depends on

- [Positivity of hermitian line bundles](../positivity-of-hermitian-line-bundles.md), for ample (Zhang's and Moriwaki's sense), nef and strongly big
- [Arithmetic volume](arithmetic-volume.md), for $\widehat{\mathrm{vol}}$ on $\widehat{\mathrm{Pic}}(X) \otimes \mathbb{Q}$
- [Arithmetic degree and arithmetic intersection numbers](../arithmetic-intersection-numbers.md), for $(\bar L^{d+1})$ and $(\bar L^d \cdot \bar M)$
- [Arithmetic varieties and hermitian vector bundles](../arithmetic-variety.md), for $\chi_{\sup}$

## Proof depends on

- [Arithmetic Hilbert–Samuel theorem](../arithmetic-hilbert-samuel-theorem.md), in Yuan's proof (Proposition 2.8 through Corollary 2.7, and the last step of Section 2.5.1)
- [Estimates for small sections along an effective divisor](estimates-for-small-sections-along-a-divisor.md), for the Bertini step of Section 2.3.3 and the estimates of Theorems 2.10–2.11, Propositions 2.12–2.14 and Lemmas 2.15–2.16, which bound the logarithm of the number of small sections
- [Small elements of normed lattices](../small-elements-of-normed-lattices.md), for the lower bound of the number of small sections by $\chi_{\sup}$ (Moriwaki's Proposition 2.1 (1)) in Moriwaki's extension
- [Zhang's arithmetic ampleness theorem](../arithmetic-ampleness-theorem.md), for the bases of small sections in Yuan's Corollary 2.7
- [Ampleness of nef plus ample hermitian line bundles](../ampleness-of-nef-plus-ample-hermitian-line-bundles.md), for the ampleness of $\bar L + \varepsilon \bar A$ and $\bar M + \varepsilon \bar A$ for nef $\bar L$, $\bar M$ and ample $\bar A$ in Moriwaki's extension (proof of Theorem 5.6)
- [Arithmetic volume](arithmetic-volume.md), for the homogeneity used in Moriwaki's extension
- [Resolution of singularities of quasi-projective varieties](../../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md), for the generic resolution in Yuan's reduction (Section 2.3.3)

## Sources

- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: Section 2.1, p. 8;
  Definition 2.1, Theorem 2.2 and the Remark after it (the meaning of the error term), p. 10;
  Corollary 2.7 and Proposition 2.8, pp. 16–18; Section 2.3.3 with Lemma 2.9, pp. 18–20; Sections
  2.4 and 2.5.1 (proof of Theorem 2.2), pp. 20–30.
- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Theorem 5.6 with
  its proof, p. 39; Proposition 2.1 (1), p. 13.
