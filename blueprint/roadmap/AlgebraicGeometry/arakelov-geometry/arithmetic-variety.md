# Arithmetic varieties and hermitian vector bundles

An arithmetic ring is a triple $(A, \Sigma, F_\infty)$ consisting of an excellent regular Noetherian
integral domain $A$, a finite nonempty set $\Sigma$ of injective ring homomorphisms $\sigma \colon A
\to \mathbb{C}$, and a conjugate-linear involution of $\mathbb{C}$-algebras $F_\infty \colon
\mathbb{C}^\Sigma \to \mathbb{C}^\Sigma$ with $F_\infty \circ \delta = \delta$, where $\delta \colon
A \to \mathbb{C}^\Sigma$ has the $\sigma \in \Sigma$ as components. The main example is the ring of
integers $\mathcal{O}_K$ of a number field $K$, or a localization of it, with $\Sigma$ the set of
all embeddings of $\mathcal{O}_K$ into $\mathbb{C}$ and $F_\infty$ induced by complex conjugation;
$\mathbb{Z}$ is an initial object of the category of arithmetic rings.

Let $F$ be the fraction field of $A$. An arithmetic variety over $A$ is a scheme $X$, flat and of
finite type over $\operatorname{Spec} A$, whose generic fibre $X_F$ is smooth over $F$. For $\sigma
\in \Sigma$ put $X_\sigma = X \otimes_\sigma \mathbb{C}$; the set of complex points $X_\infty =
\coprod_{\sigma \in \Sigma} X_\sigma(\mathbb{C})$ is a complex manifold, on which $F_\infty$ induces
an involution, again written $F_\infty$. Let $A^{p,q}(X)$ and $\mathcal{D}^{p,q}(X)$ be the spaces
of smooth forms and of currents of type $(p, q)$ on $X_\infty$, and $A^{p,p}(X_\mathbb{R})$,
$\mathcal{D}^{p,p}(X_\mathbb{R})$ the subspaces of real forms and currents $\alpha$ with $F_\infty^*
\alpha = (-1)^p \alpha$. The differential operators are normalized by $d = \partial + \bar\partial$
and $d^c = \frac{i}{4\pi}(\bar\partial - \partial)$, so that $dd^c = \frac{i}{2\pi}
\partial\bar\partial$; $dd^c$ maps $A^{p,p}(X_\mathbb{R})$ to $A^{p+1,p+1}(X_\mathbb{R})$ and
$\mathcal{D}^{p,p}(X_\mathbb{R})$ to $\mathcal{D}^{p+1,p+1}(X_\mathbb{R})$.

A hermitian vector bundle $\bar E = (E, h)$ on an arithmetic variety $X$ is a locally free sheaf $E$
of finite rank on $X$ together with a smooth hermitian metric $h$ on the holomorphic vector bundle
induced by $E$ on $X_\infty$, invariant under $F_\infty$. If $f \colon Y \to X$ is a morphism of
arithmetic varieties, $f^* \bar E = (f^* E, f^* h)$ is a hermitian vector bundle on $Y$. A hermitian
line bundle $\bar L = (L, \lVert \cdot \rVert)$ is a hermitian vector bundle of rank one, and
$\widehat{\mathrm{Pic}}(X)$ is the group, under tensor product, of isometry classes of hermitian
line bundles on $X$. The same definitions make sense on any scheme flat and of finite type over $A$
with smooth generic fibre; Gillet and Soulé's arithmetic Riemann–Roch paper works, in its §§2–3,
with arithmetic varieties quasi-projective over a good arithmetic ring, that is, one that is
equicodimensional and Jacobson.

Chambert-Loir works more generally with a proper flat scheme $X$ over $\mathbb{Z}$, whose analytic
space $X(\mathbb{C})$ is smooth exactly when $X_\mathbb{Q}$ is regular. A function on
$X(\mathbb{C})$ is smooth if it extends to a smooth function around the image of every local
embedding of an open subset of $X(\mathbb{C})$ into some $\mathbb{C}^n$. A hermitian metric on a
line bundle $L$ assigns to every section $s$ of $L$ over an open subset $U$ of $X(\mathbb{C})$ a
continuous function $\lVert s \rVert \colon U \to \mathbb{R}_{\ge 0}$, compatible with restriction,
with $\lVert f s \rVert = |f| \, \lVert s \rVert$ for holomorphic $f$, and strictly positive and
smooth where $s$ does not vanish; no invariance under complex conjugation is required, so
Chambert-Loir's group $\widehat{\mathrm{Pic}}(X)$ is not literally the group of Gillet and Soulé.
With these conventions the sequence

$$\Gamma(X, \mathcal{O}_X^\times) \to C^\infty(X(\mathbb{C}), \mathbb{R}) \to
\widehat{\mathrm{Pic}}(X) \to \mathrm{Pic}(X) \to 0$$

is exact, where the first map is $f \mapsto \log|f|$, the second sends $\varphi$ to $\mathcal{O}_X$
with the metric for which $\log \lVert 1 \rVert^{-1} = \varphi$, and the third forgets the metric.
The current $-\log \lVert 1 \rVert^2$ for this metric is $2\varphi$; it is a Green current in Gillet
and Soulé's sense, a real current invariant under complex conjugation, only when $\varphi$ is
invariant.

Let $\bar L$ be a hermitian line bundle on an arithmetic variety $X$ projective over
$\operatorname{Spec} \mathbb{Z}$. Then $H^0(X, L)$ is a finitely generated $\mathbb{Z}$-module, and
$H^0(X, L) \otimes_\mathbb{Z} \mathbb{R}$ is the real subspace of the space of sections of $L$ over
$X(\mathbb{C})$ formed by the sections compatible with complex conjugation; the sup norm is $\lVert
s \rVert_{\sup} = \sup_{x \in X(\mathbb{C})} \lVert s(x) \rVert$. When $X(\mathbb{C})$ is a compact
complex manifold with a volume form $\Omega$, the $L^2$ norm is $\lVert s \rVert_{L^2} = \bigl(
\int_{X(\mathbb{C})} \lVert s \rVert^2 \, \Omega \bigr)^{1/2}$. The lattice invariants used below
are

$$\hat h^0(\bar L) = \log \#\{ s \in H^0(X, L) : \lVert s \rVert_{\sup} \le 1 \}$$

and, when $H^0(X, L)$ is torsion-free,

$$\chi_{\sup}(\bar L) = \log \frac{\operatorname{vol}(B_{\sup})}
{\operatorname{vol}\bigl(H^0(X, L)_\mathbb{R} / H^0(X, L)\bigr)}, \qquad
B_{\sup} = \{ s \in H^0(X, L)_\mathbb{R} : \lVert s \rVert_{\sup} < 1 \},$$

which does not depend on the choice of Haar measure on $H^0(X, L)_\mathbb{R}$. Moriwaki writes $\hat
h^0(H^0(X, L), \lVert \cdot \rVert_{\sup})$ for the first number; Yuan's $h^0(\bar L)$ is the
logarithm of the number of sections with $\lVert s \rVert_{\sup} < 1$ instead.

In the work of Zhang, Moriwaki and Yuan on heights, volumes and positivity, an arithmetic variety of
dimension $d + 1$ is an integral scheme $X$, projective and flat over $\operatorname{Spec}
\mathbb{Z}$, of absolute dimension $d + 1$; Moriwaki allows quasi-projective $X$ and calls $X$ a
projective arithmetic variety when it is projective. Such an $X$ need not be regular, and its
generic fibre $X_\mathbb{Q}$, of dimension $d$, need not be smooth; $X$ is generically smooth if
$X_\mathbb{Q}$ is smooth over $\mathbb{Q}$. A metric on $L_\mathbb{C}$ is smooth if its pull-back by
every analytic map from the unit polydisc of $\mathbb{C}^d$ to $X(\mathbb{C})$ is smooth, and a
hermitian line bundle carries a smooth metric invariant under complex conjugation; this is Zhang's
and Yuan's convention, not a theorem comparing it with Chambert-Loir's definition by local ambient
extensions. A generic resolution of singularities of $X$ is a projective birational morphism $\mu
\colon X' \to X$ of arithmetic varieties with $X'$ generically smooth. One exists: resolve the
singularities of the generic fibre $X_\mathbb{Q}$ by a projective birational morphism $X'_\mathbb{Q}
\to X_\mathbb{Q}$ from a smooth variety, embed $X'_\mathbb{Q}$ in a projective space over
$X_\mathbb{Q}$, and take the reduced closure $X'$ of its image in the corresponding projective space
over $X$; it is integral, dominates $\operatorname{Spec} \mathbb{Z}$, hence is flat over
$\mathbb{Z}$, and is projective and birational over $X$. It need not be regular at the finite
places.

## Depends on

- [Currents of integration and the support theorems](../birational-geometry/currents-of-integration.md),
  for the currents of type $(p, q)$ on $X_\infty$

## Proof depends on

- [Resolution of singularities of quasi-projective varieties](../birational-geometry/resolution-of-singularities/resolution-of-singularities-of-quasi-projective-varieties.md), for the resolution of the generic fibre in the existence of a generic resolution of singularities
- [Standard results of coherent cohomology on projective varieties](../birational-geometry/standard-results-of-coherent-cohomology.md),
  for the finiteness theorem, which makes $H^0(X, L)$ a finitely generated $\mathbb{Z}$-module for
  $X$ projective over $\mathbb{Z}$, and for flat base change along the flat ring map $\mathbb{Z} \to
  \mathbb{C}$ and GAGA, which identify $H^0(X, L) \otimes_\mathbb{Z} \mathbb{C}$ with the
  holomorphic sections of $L$ over $X(\mathbb{C})$

## Sources

- H. Gillet and C. Soulé, "Arithmetic intersection theory", Publ. Math. IHÉS 72 (1990), 93–174,
  <http://www.numdam.org/item/PMIHES_1990__72__93_0/>: 1.1.6 (ii) (the normalization of $d^c$, p.
  100), Definition 3.1.1, Examples 3.1.2 and §3.1.3 (arithmetic rings and their morphisms, pp.
  124–125), Definition 3.2.1 (arithmetic varieties, $X_\infty$, $F_\infty$, $A^{p,p}(X_\mathbb{R})$
  and $\mathcal{D}^{p,p}(X_\mathbb{R})$, p. 125), 3.4.2 ($\widehat{\mathrm{Pic}}(X)$, p. 131).
- H. Gillet and C. Soulé, "An arithmetic Riemann–Roch theorem", Invent. Math. 110 (1992), 473–543,
  <https://gdz.sub.uni-goettingen.de/id/PPN356556735_0110>: introduction (p. 473), §2.1 (good
  arithmetic rings and quasi-projective arithmetic varieties, p. 484) and 2.4.2 (p. 495), hermitian
  vector bundles and their pull-backs.
- J.-B. Bost, H. Gillet and C. Soulé, "Heights of projective varieties and positive Green forms", J.
  Amer. Math. Soc. 7 (1994), 903–1027: §2.1.2, p. 932 (hermitian vector bundles).
- S.-W. Zhang, "Positive line bundles on arithmetic varieties", J. Amer. Math. Soc. 8 (1995),
  187–221, author's scan of the printed edition
  <https://web.math.princeton.edu/~shouwu/publications/plav.pdf>: §§1.1–1.2, pp. 188–189 (arithmetic
  varieties of dimension $d + 1$, smooth metrics, generic resolutions).
- A. Chambert-Loir, "Arakelov geometry, heights, equidistribution, and the Bogomolov conjecture",
  arXiv:1904.05630v3 (2020), in *Arakelov Geometry and Diophantine Applications*, Lecture Notes in
  Math. 2276, <https://arxiv.org/abs/1904.05630v3>: 2.1 and 2.3 with the exact sequence (2.3.1), pp.
  2–3.
- A. Moriwaki, "Continuity of volumes on arithmetic varieties", J. Algebraic Geom. 18 (2009),
  407–457, arXiv:math/0612269 (version 2), <https://arxiv.org/abs/math/0612269v2>: Conventions and
  terminology 5 (sup and $L^2$ norms) and 6 (arithmetic varieties, generic smoothness, generic
  resolutions of singularities), pp. 4–5; Section 2 ($\hat H^0$ and $\hat h^0$ of a normed
  $\mathbb{Z}$-module), p. 12.
- X. Yuan, "Big line bundles over arithmetic varieties", Invent. Math. 173 (2008), 603–649,
  arXiv:math/0612424 (version 2), <https://arxiv.org/abs/math/0612424v2>: Section 2.1 (arithmetic
  varieties of dimension $n$, smooth metrics and hermitian line bundles, the sup norm, $h^0$ and
  $\chi_{\sup}$), p. 8.
