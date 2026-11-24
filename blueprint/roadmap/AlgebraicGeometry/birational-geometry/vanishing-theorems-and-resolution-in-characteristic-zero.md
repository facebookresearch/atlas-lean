# Vanishing theorems and resolution of singularities in characteristic zero

This node covers resolution of singularities and principalization of ideals over fields of
characteristic zero, the vanishing theorems of Kodaira, Kawamata–Viehweg and Nadel with multiplier
ideals, the volume of a line bundle, the Ohsawa–Takegoshi $L^2$ extension theorem and the
Poincaré–Lelong formula. In the vanishing theorems $X$ is a smooth projective variety of dimension
$n$, over a field of characteristic zero for the Kodaira and Kawamata–Viehweg theorems and over
$\mathbb{C}$ for multiplier ideals; the analytic statements are over $\mathbb{C}$.

- **Principalization.** Let $X$ be a smooth scheme of finite type over a field of characteristic
  zero, $I \subset \mathcal{O}_X$ an ideal sheaf that is nonzero on every irreducible component of
  $X$, and $E$ a divisor with simple normal crossings. There is a composite
  $\Pi \colon X' \to X$ of blow-ups of smooth centres having simple normal crossings with $E$ such
  that $\Pi^{-1} I \cdot \mathcal{O}_{X'}$ is the ideal sheaf of a divisor with simple normal
  crossings and $\Pi$ is an isomorphism outside the cosupport of $I$; it can be chosen functorial
  for smooth morphisms.
- **Resolution of singularities** (Hironaka). Every quasi-projective variety $X$ over a field of
  characteristic zero has a projective birational morphism $\Pi \colon X' \to X$ with $X'$ smooth
  that is an isomorphism over the smooth locus of $X$ and such that $\Pi^{-1}(\operatorname{Sing} X)$
  is a divisor with simple normal crossings. The resolution comes from a principalization in a
  smooth ambient variety, and it need not be a composite of blow-ups of smooth centres of $X$.
- **Resolution of schemes of finite type.** For every scheme $X$ of finite type over a field of
  characteristic zero, possibly nonreduced, there is a sequence of blow-ups
  $\Pi \colon X_r \to \dots \to X_0 = X$, functorial for smooth morphisms and for change of fields,
  with $X_r$ smooth, $\Pi$ an isomorphism over the smooth locus of $X$, and
  $\Pi^{-1}(\operatorname{Sing} X)$ a divisor with simple normal crossings. This statement does not
  include birationality.
- **Kodaira vanishing.** For an ample line bundle $A$ on $X$,
  $H^i(X, \omega_X \otimes A) = 0$ for $i > 0$.
- **Kawamata–Viehweg vanishing.** Let $L$ be an integral divisor and $D$ an effective
  $\mathbb{Q}$-divisor with simple normal crossing support such that $L - D$ is nef and big. Then
  $H^i(X, \mathcal{O}_X(K_X + L - \lfloor D \rfloor)) = 0$ for $i > 0$.
- **Multiplier ideals and Nadel vanishing.** For an effective $\mathbb{Q}$-divisor $D$ with log
  resolution $\mu \colon X' \to X$, the multiplier ideal is
  $\mathcal{J}(D) = \mu_* \mathcal{O}_{X'}(K_{X'/X} - \lfloor \mu^* D \rfloor)$. If $L$ is an integral
  divisor with $L - D$ nef and big, then $H^i(X, \mathcal{O}_X(K_X + L) \otimes \mathcal{J}(D)) = 0$
  for $i > 0$. Analytically (Nadel): if $(X, \omega)$ is a weakly pseudoconvex Kähler manifold and
  $F$ a line bundle with a singular hermitian metric $h$ such that
  $i\Theta_{F,h} \ge \varepsilon\omega$ for a continuous positive function $\varepsilon$, then
  $H^q(X, \mathcal{O}(K_X + F) \otimes \mathcal{I}(h)) = 0$ for $q \ge 1$, where $\mathcal{I}(h)$ is
  the multiplier ideal sheaf of the weight of $h$.
- **Volume.** For a line bundle $L$ on a compact complex manifold $X$ of dimension $n$, the volume
  $\operatorname{vol}(L) = \limsup_{k \to \infty} \frac{n!}{k^n} h^0(X, kL)$ is finite, and $L$ is
  big if and only if $\operatorname{vol}(L) > 0$. If $X$ is Kähler and $L$ is nef, then
  $\operatorname{vol}(L) = (L^n)$.
- **$L^2$ extension** (Ohsawa–Takegoshi). Let $\Omega \subset \mathbb{C}^n$ be a bounded
  pseudoconvex domain, $\psi$ a plurisubharmonic function on $\Omega$ and $H$ a complex hyperplane.
  There is a constant $C$ depending only on the diameter of $\Omega$ such that every holomorphic
  function $f$ on $\Omega \cap H$ with $\int_{\Omega \cap H} e^{-\psi} \lvert f \rvert^2 < \infty$
  extends to a holomorphic function $F$ on $\Omega$ with
  $\int_{\Omega} e^{-\psi} \lvert F \rvert^2 \le C \int_{\Omega \cap H} e^{-\psi} \lvert f \rvert^2$.
- **Poincaré–Lelong formula.** For a meromorphic function $f$ on a complex manifold that does not
  vanish identically on any connected component, with divisor $\sum_j m_j Z_j$, the function
  $\log \lvert f \rvert$ is locally integrable and
  $\frac{i}{\pi} \partial \bar\partial \log \lvert f \rvert = \sum_j m_j [Z_j]$ as currents; with
  $d^c = \frac{i}{4\pi}(\bar\partial - \partial)$ this reads
  $dd^c \log \lvert f \rvert^2 = \sum_j m_j [Z_j]$.

Linear systems and birational maps of particular varieties are outside this node.

## Expansion

A good expansion replaces this node by definition pages and statements in the following order,
each citing the source and locator below.

1. Blow-ups, divisors with simple normal crossings and log resolutions; principalization, then
   resolution of quasi-projective varieties, deduced from it, and the functorial resolution of
   schemes of finite type.
2. Nef and big divisors, the volume and its properties.
3. Kodaira vanishing, then Kawamata–Viehweg vanishing, whose statement uses the divisors of step 1
   and the positivity notions of step 2.
4. Multiplier ideals of $\mathbb{Q}$-divisors and Nadel vanishing; then the analytic multiplier
   ideal sheaves and Nadel's theorem.
5. Currents and the Poincaré–Lelong formula; $L^2$ estimates for $\bar\partial$ and the
   Ohsawa–Takegoshi extension theorem.

## Sources

- J. Kollár, "Resolution of singularities – Seattle lecture", arXiv:math/0508332 (version 3), §3:
  Theorems 21 and 26 (principalization), Corollary 22 and Warning 23 (resolution from
  principalization; its centres need not be smooth), Theorem 27 (resolution of quasi-projective
  varieties), Theorem 35 (functorial principalization) and Theorem 36 (functorial resolution of
  schemes of finite type). This lecture is the chapter "Strong resolution
  in characteristic zero" of J. Kollár, *Lectures on Resolution of Singularities*, Annals of
  Mathematics Studies 166, Princeton University Press, 2007. The theorem is due to H. Hironaka,
  "Resolution of singularities of an algebraic variety over a field of characteristic zero. I, II",
  Ann. of Math. (2) 79 (1964), 109–203 and 205–326.
- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>:
  Theorem 1.2 and the remark after it (Kodaira vanishing), Corollary 5.12 c) (Kawamata–Viehweg
  vanishing over a field of characteristic zero, which for $D = 0$ contains Kodaira vanishing in
  its Serre-dual form).
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1): Definition 1.3
  (multiplier ideals), Theorem 2.2 (Kawamata–Viehweg vanishing), Theorem 2.4 (Nadel vanishing). See
  also R. Lazarsfeld, *Positivity in Algebraic Geometry I, II*, Ergebnisse der Mathematik 48, 49,
  Springer, 2004: the chapters "Vanishing Theorems" (volume I, pp. 239–267) and "Multiplier Ideal
  Sheaves" (volume II, pp. 139–231).
- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: (1.20)
  (Lelong–Poincaré equation), Definition (5.4) and Theorem (5.11) (multiplier ideal sheaves, Nadel
  vanishing), (6.12)–(6.13) (Kodaira–Iitaka dimension and volume, with the remark after (6.13) on
  nef line bundles), Theorem (6.25), §13, Theorem (13.6) and Corollary (13.9) ($L^2$ extension).
- T. Ohsawa and K. Takegoshi, "On the extension of $L^2$ holomorphic functions", Math. Z. 195
  (1987), 197–204, <https://gdz.sub.uni-goettingen.de/id/PPN266833020_0195>: the Theorem of the
  introduction.
- J.-P. Demailly, *Complex Analytic and Differential Geometry*, version of 21 June 2012,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf>: Chapter III,
  (2.15) (Lelong–Poincaré equation).
- Proof of the Riemann hypothesis and of the generalized Riemann hypothesis for Dirichlet
  L-functions: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>).
  Statement and proof of the Riemann hypothesis certified by the Lean and Mathlib communities in a
  joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative
  (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); independent checks of
  its five main theorems by A. Sutherland (<https://math.mit.edu/~drew/grh/>). Source mirror:
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>.
  Related formal statements in Alpöge's proof, often in specialised forms,
  include `GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero`,
  `GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero`,
  `GlobalTheory.Published.KawamataViehweg`, `GlobalTheory.Published.NadelVanishingAndNonKltDivisor`,
  `GlobalTheory.Published.L2ExtensionLogCanonical` and `GlobalTheory.Published.NefNumerics`.
