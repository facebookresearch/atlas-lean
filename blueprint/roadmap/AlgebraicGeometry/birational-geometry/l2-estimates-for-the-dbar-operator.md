# L² estimates for the ∂̄ operator

This node is still to be broken down. It covers the $L^2$ existence theorems for the $\bar\partial$
operator on Kähler manifolds, going back to Kohn, Andreotti–Vesentini and Hörmander, and the
analytic methods built on them that the
[Nadel vanishing theorem for singular hermitian metrics](nadel-vanishing-for-singular-hermitian-metrics.md),
the [Ohsawa–Takegoshi extension theorem](ohsawa-takegoshi-extension-theorem.md) and the
[volume of nef line bundles](volume-of-a-line-bundle.md) use. It follows Demailly's *Analytic
Methods in Algebraic Geometry*, §§4, 5, 8 and 13, and §§1–2 of Ohsawa–Takegoshi.

Its basic statement is Demailly's Theorem 5.1: let $(X, \omega)$ be a Kähler manifold whose geodesic
distance is complete and $F$ a hermitian vector bundle on $X$ whose curvature operator $A =
[i\Theta_{F,h}, \Lambda_\omega]$ is positive definite on $\Lambda^{p,q} T^*_X \otimes F$ for some $q
\ge 1$. Then for every $g \in L^2(X, \Lambda^{p,q} T^*_X \otimes F)$ with $D'' g = 0$ and $\int_X
\langle A^{-1} g, g \rangle \, dV_\omega < \infty$ there is $f \in L^2(X, \Lambda^{p,q-1} T^*_X
\otimes F)$ with $D'' f = g$ and $\int_X |f|^2 \, dV_\omega \le \int_X \langle A^{-1} g, g \rangle
\, dV_\omega$.

A good expansion has pages for:

- the commutation relations of Kähler geometry and the Bochner–Kodaira–Nakano identity $\Delta'' =
  \Delta' + [i\Theta_{F,h}, \Lambda]$ on Kähler manifolds (Demailly (4.5)–(4.6)), with the a priori
  inequality (4.7) and the computation (4.10) of the curvature term for line bundles;
- the $L^2$ existence theorem (5.1) on Kähler manifolds with complete geodesic distance; its form
  (5.2) for a line bundle with positive curvature on a weakly pseudoconvex Kähler manifold, with the
  estimate by the sum $\gamma_1 + \dots + \gamma_q$ of the smallest curvature eigenvalues, which
  extends to singular metrics with positive curvature current by regularization (the remark after
  (5.2)); and Corollary (5.3) on a weakly pseudoconvex Kähler manifold, for a line bundle with a
  singular metric written as the quadratic form $H = e^{-\varphi}$ with $\varphi \in
  L^1_{\mathrm{loc}}$ and $i\Theta_{F,h} = i\partial\bar\partial \varphi \ge \varepsilon\omega$ for
  a constant $\varepsilon > 0$: every $D''$-closed $g \in L^2(X, \Lambda^{n,q} T^*_X \otimes F)$, $q
  \ge 1$, is $D'' f$ with $\int_X |f|^2 e^{-\varphi} \, dV_\omega \le \frac{1}{q\varepsilon} \int_X
  |g|^2 e^{-\varphi} \, dV_\omega$. Here the weight is $e^{-\varphi}$, whereas the Nadel vanishing
  theorem writes the norm as $|\theta(\xi)| e^{-\varphi}$, with weight $e^{-2\varphi}$, and allows a
  continuous positive function $\varepsilon$, which on a noncompact manifold need not be bounded
  below by a positive constant; the coherence of multiplier ideal sheaves (5.7) and the local
  exactness in the proof of the Nadel vanishing theorem (5.11) rest on this corollary, and the
  global step of (5.11) on (5.2) for singular metrics;
- Ohsawa's twisted a priori inequality (Demailly, Lemma 13.1 and (13.3)), the existence theorem
  (13.4) deduced from it and its approximate form (13.5), which Demailly uses for the extension
  theorem (13.6); and, for Ohsawa and Takegoshi's own proof, the identities of their §1 (after
  Calabi–Vesentini and Nakano), the a priori estimate of their §2, Proposition 1, for the operator
  $\bar\partial \circ \eta$, and their Theorem 2, which they derive from Andreotti and Vesentini's
  theorem and the Hahn–Banach theorem, together with the smooth strictly plurisubharmonic exhaustion
  functions of Stein manifolds (their §3, Proposition 3);
- the holomorphic Morse inequalities (Demailly (8.1)–(8.2)) for a hermitian line bundle on a compact
  complex manifold, proved through the spectral theory of the complex Laplace operator (Demailly
  refers to [Dem85b, 91] for the analytic details), and their Corollary (8.4): $h^q(X,
  \mathcal{O}(E) \otimes \mathcal{O}(kL)) = o(k^n)$ for $q \ge 1$ when $X$ is compact Kähler and $L$
  is nef. With the Riemann–Roch formula $\chi(X, kL) = \frac{(L^n)}{n!} k^n + o(k^n)$ this gives
  $\operatorname{Vol}(L) = (L^n)$ for nef $L$ (proof of Corollary (6.19)). The remark after (6.13)
  refers to Corollary (8.4) as "Corollary 8.3";
- the Riemann–Roch formula $\chi(X, kL) = \frac{(L^n)}{n!} k^n + o(k^n)$ on a compact complex
  manifold, a consequence of the Hirzebruch–Riemann–Roch theorem in that generality, which the
  standard results of coherent cohomology state only for smooth projective varieties; Esnault and
  Viehweg also use it, for their Lemma 5.8;
- complete Kähler metrics: every weakly pseudoconvex Kähler manifold carries one (Demailly, the
  observation before (5.2), p. 34), and so does $X_c \setminus Y$ for $X$ weakly pseudoconvex
  Kähler, exhausted by the sublevel sets $X_c$, and $Y = \sigma^{-1}(0)$ an analytic subset defined
  by a section of a hermitian vector bundle (Lemma (12.9), p. 116), so that (5.1) applies on the
  complement of the polar set of a weight. For an arbitrary analytic subset $Z$, $\Omega \setminus
  Z$ is complete Kähler whenever $\Omega$ is a relatively compact open subset of a Kähler manifold
  and $\Omega$ itself carries a complete Kähler metric, in particular for the sublevel sets $\Omega
  = X_c$ of a weakly pseudoconvex $X$ (Demailly 1982, Théorème 1.5 and Remarque 1.6, p. 464);
- the Serre–Siegel lemma (Demailly (6.13), p. 45, proved from the Schwarz lemma on polydiscs, which
  reduces to the unit disc along complex lines through the centre): for a holomorphic line bundle
  $L$ on a compact complex manifold with $\kappa(L) \ge 0$, $h^0(X, mL) = O(m^{\kappa(L)})$ for $m
  \ge 1$ and $\kappa(L)$ is the smallest exponent with this property, while $h^0(X, mL) = 0$ for all
  $m \ge 1$ when $\kappa(L) = -\infty$; the volume is finite, and $L$ is big if and only if its
  volume is positive.

## Depends on

- [Currents of integration and the support theorems](currents-of-integration.md), for the curvature
  currents of singular metrics in Corollary (5.3)

## Proof depends on

- [Schwarz–Pick lemma](../../Analysis/complex-analysis/geometric-function-theory/schwarz-pick-lemma/schwarz-pick.md),
  for the Schwarz bound $|f(z)| \le |z|$ on the unit disc, its case $w = 0$ when $f(0) = 0$, to
  which the Schwarz lemma on polydiscs behind the Serre–Siegel lemma (6.13) reduces
- [Hahn–Banach extension with the same norm](../../Analysis/banach-spaces/duality-and-weak-topologies/hahn-banach-theorem/hahn-banach-norm-preserving-extension.md),
  for the extension of the bounded functional $D''^* v \mapsto \langle v, g \rangle$ from the range
  of $D''^*$ to the whole $L^2$ space with the same norm, in the proof of (5.1)
- [Riesz representation theorem](../../Analysis/hilbert-spaces/riesz-representation-hilbert.md), for
  the vector of the Hilbert space that represents the extended functional, in the proof of (5.1)

## Expansion

A good expansion also states and links:

- Kähler manifolds with complete metrics and hermitian vector bundles with their curvature operators
  on $L^2$ forms (Demailly, §§4–5), for the statement
- the cut-off functions that the completeness of the metric provides (Demailly, proof of (5.1)),
  for the passage from the a priori inequality (4.7) to (5.1)

## Sources

- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: (3.10) (the
  notations $e^{-2\varphi}$ and $e^{-\varphi}$ for the metric of a line bundle), pp. 25–26, and
  Definition (3.12) ($\lVert \xi \rVert_h = |\theta(\xi)| e^{-\varphi}$ for singular metrics), p.
  26; §4.C, (4.5)–(4.7), p. 30, and (4.10), p. 31; §5.A, Theorems (5.1) and (5.2) and Corollary
  (5.3), pp. 32–35; Proposition (5.7), p. 37; Theorem (5.11), p. 39; §8.A, (8.1)–(8.4), pp. 62–63;
  §13.A–B, Lemma (13.1), (13.3), Proposition (13.4) and Remark (13.5), pp. 122–125; Lemma (6.13) and
  the remark after it, p. 45; Lemma (6.18) and Corollary (6.19), p. 48.
- J.-P. Demailly, "Estimations $L^2$ pour l'opérateur $\bar\partial$ d'un fibré vectoriel holomorphe
  semi-positif au-dessus d'une variété kählérienne complète", Ann. Sci. École Norm. Sup. (4) 15
  (1982), 457–511: Théorème 1.5 and Remarque 1.6, p. 464.
- T. Ohsawa and K. Takegoshi, "On the extension of $L^2$ holomorphic functions", Math. Z. 195
  (1987), 197–204, <https://gdz.sub.uni-goettingen.de/id/PPN266833020_0195>: §1, p. 198; §2,
  Proposition 1, p. 199, and Theorem 2, p. 200; §3, Proposition 3, p. 200.
- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): the proof of Lemma 5.8, p. 47.
