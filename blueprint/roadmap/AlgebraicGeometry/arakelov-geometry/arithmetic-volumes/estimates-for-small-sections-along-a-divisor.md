# Estimates for small sections along an effective divisor

This node is still to be broken down. It covers the analytic and arithmetic estimates by which Yuan
proves his [inequality for arithmetic volumes](yuan-inequality.md): the existence of small sections
whose divisors avoid prescribed points (arithmetic Bertini theorems), the asymptotics of distortion
functions of positive hermitian line bundles, and the comparison of Euler characteristics along the
divisor of a small section.

A good expansion has pages for:

- Moriwaki's small-section Bertini theorem: let $X$ be an integral arithmetic variety, projective
  and flat over $\mathbb{Z}$ with smooth generic fibre, and $\bar H$ a hermitian line bundle that is
  arithmetically ample in Moriwaki's sense ($H$ relatively ample, the metric of positive curvature,
  and every horizontal subvariety of positive height); let $x_1, \dots, x_r$ be finitely many points
  with residue fields of positive characteristic, and $Z_m$ **decomposable** hypersurfaces of the
  linear systems $|H^m_\infty|$ on the possibly disconnected complex fibre, that is, sums of
  pull-backs of hypersurfaces of the linear systems of its connected components (§4, p. 12; a
  diagonal in a product of two projective lines is a hypersurface that is not decomposable), with
  degrees bounded by a polynomial in $m$. Then for every large $m$ there is $\varphi \in H^0(X,
  H^m)$ with $\varphi(x_i) \ne 0$ for all $i$, $\operatorname{div}(\varphi_\infty) \notin Z_m$ and
  $\lVert \varphi \rVert_{\sup} < 1$ (Moriwaki, "Arithmetic Bogomolov–Gieseker's inequality",
  Theorem 5.3, pp. 17–18, whose proof uses Zhang's bases of small sections of
  [arithmetically ample](../arithmetic-ampleness-theorem.md) bundles, Zhang's Corollary 4.8); and its
  use in Yuan §2.3.3, pp. 18–20, where the Bertini step avoids the generic points of the bad
  vertical components after passing to a multiple, Lipman's resolution serves in arithmetic
  dimension two, and Lemma 2.9 perturbs to positive curvature;
- the distortion function of a positive hermitian line bundle and its uniform asymptotics $b(E +
  NL)(z) = \dim \Gamma(E + NL) (1 + O(1/N))$ for the measure induced by $L$ (Bouche, Tian; Yuan,
  Theorem 2.11, p. 21) and the upper bound for $E + NL - jM$ (Proposition 2.12, p. 22);
- Yuan's chain of comparisons along the divisor: Theorem 2.10 (p. 21, proved p. 23), a lower bound
  for $\chi_{L^2} - \chi_s$ involving $\int \log |s| \, d\mu$; Proposition 2.14 (p. 25), a
  difference of two $\chi_{L^2}$ involving the mixed intersection, for normal, generically smooth
  $X$, positive curvatures, a strictly small section of $M'$ and Cartier components of its divisor,
  with Lemmas 2.15–2.16, pp. 25–29, which use the classical Hilbert–Samuel formula on the vertical
  components and the arithmetic one on the horizontal components; and the passage between sup and
  $L^2$ norms (Corollary 2.7 (2) and Proposition 2.13, through
  [Gromov's inequality](../gromov-inequality.md)), in this order, the inequalities being obtained for
  $\chi_{L^2}$ and transferred to $\chi_{\sup}$;
- Moriwaki's analytic estimates in §1 of "Continuity of volumes on arithmetic varieties", used in
  his fundamental estimate: the distortion estimate Theorem 1.2.1 (after Bouche and Tian) and its
  Corollary 1.2.2, pp. 11–12; Lemma 1.1.4, bounding the $L^2$ norm by the $L^2$ norm on an open
  subset meeting every component; and Corollary 1.1.3, on restriction to a smooth submanifold.

## Depends on

- [Positivity of hermitian line bundles](../positivity-of-hermitian-line-bundles.md)

## Proof depends on

- [Gromov's inequality](../gromov-inequality.md), for Yuan's Proposition 2.13
- [Arithmetic Hilbert–Samuel theorem](../arithmetic-hilbert-samuel-theorem.md), on the horizontal
  components, in Yuan's Lemmas 2.15–2.16
- [Arithmetic ampleness theorem](../arithmetic-ampleness-theorem.md), for Zhang's Corollary 4.8, the bases
  of small sections in the proof of Moriwaki's Theorem 5.3
- [Extension of small sections and bases of small sections](../extension-of-small-sections.md), for the
  steps of Zhang's proof of these bases

## Sources

- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: Corollary 2.7 (2), §2.3.3
  with Lemma 2.9, pp. 18–20; Theorem 2.10, p. 21, with its proof, p. 23; Theorem 2.11 (distortion
  functions), p. 21; Propositions 2.12–2.14, pp. 22–25; Lemmas 2.15–2.16, pp. 25–29.
- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Corollary 1.1.3,
  Lemma 1.1.4, Theorem 1.2.1 and Corollary 1.2.2, pp. 8–12.
- A. Moriwaki, "Arithmetic Bogomolov–Gieseker's inequality", arXiv:alg-geom/9307004 (version 1),
  <https://arxiv.org/abs/alg-geom/9307004v1>: introduction, p. 2; §4 (decomposable hypersurfaces),
  Theorem 4.2 and Corollary 4.3, p. 12; Theorem 5.3 with its proof, pp. 17–18.
