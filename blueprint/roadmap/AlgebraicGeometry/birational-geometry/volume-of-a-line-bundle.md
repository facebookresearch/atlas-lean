# Volume of a line bundle

Let $X$ be a compact complex manifold of dimension $n$ and $L$ a holomorphic line bundle on $X$. The
*volume* of $L$ is

$$\operatorname{Vol}(L) = \limsup_{k \to +\infty} \frac{n!}{k^n}\, h^0(X, kL), \qquad h^0(X, kL) = \dim H^0(X, kL).$$

It is finite, and $L$ is [big](nef-and-big-line-bundles.md) if and only if $\operatorname{Vol}(L) >
0$. If moreover $X$ is Kähler and $L$ is [nef](nef-and-big-line-bundles.md), then

$$\operatorname{Vol}(L) = (L^n) = \int_X c_1(L)^n;$$

in particular a nef line bundle on a compact Kähler manifold is big if and only if $(L^n) > 0$. This
applies to every ample line bundle on a projective manifold.

The first assertion is part of the Serre–Siegel lemma (Demailly (6.13)), which also says that, when
$\kappa(L) \ge 0$, $h^0(X, mL) = O(m^{\kappa(L)})$ and $\kappa(L)$ is the smallest exponent with
this property; when $\kappa(L) = -\infty$, $h^0(X, mL) = 0$ for all $m \ge 1$, which is $O(m^a)$ for
every real $a$ (as for $\mathcal{O}(-1)$ on $\mathbb{P}^1$), so that there is no smallest real
exponent. For the second, Demailly shows that $h^q(X, kL) = o(k^n)$ for $q \ge 1$ when $X$ is
compact Kähler and $L$ is nef, as a consequence of the holomorphic Morse inequalities (Corollary
8.4; the remark after (6.13) refers to it as Corollary 8.3), so that the Riemann–Roch formula gives
$h^0(X, kL) = \chi(X, kL) + o(k^n) = \frac{(L^n)}{n!} k^n + o(k^n)$ (proof of Corollary 6.19, which
states the criterion for bigness).

**Algebraic form.** Let $X$ be an integral smooth projective variety of dimension $n$ over an
algebraically closed field of characteristic zero and $L$ a nef invertible sheaf on $X$. Then
$\kappa(L) = n$ if and only if $c_1(L)^n > 0$ (Esnault–Viehweg, Lemma 5.8 a)). Their proof combines
the Hirzebruch–Riemann–Roch theorem, by which $\chi(X, L^\nu)$ is a polynomial in $\nu$ of degree at
most $n$ whose coefficient of $\nu^n$ is $c_1(L)^n / n!$ (for $L = \mathcal{O}$ on $\mathbb{P}^1$ it
is the constant $1$), with the bounds $\dim H^b(X, F \otimes L^\nu) \le c_b\, \nu^{n-b}$ for every
invertible sheaf $F$ and every $b \ge 0$ (Lemma 5.8 b)), which they prove by induction on the
dimension through hyperplane sections, from the
[Kodaira vanishing theorem](kodaira-vanishing-theorem.md) and the characterization of nef sheaves by
Seshadri's criterion (Lemma 5.7); together these give $\dim H^0(X, L^\nu) = \frac{c_1(L)^n}{n!}
\nu^n + O(\nu^{n-1})$. Lazarsfeld states the criterion for nef divisors on irreducible complex
projective varieties and notes that it holds for nef $\mathbb{Q}$-divisors (Lemma 2.1).

## Depends on

- [Nef and big line bundles](nef-and-big-line-bundles.md)
- [Geometrically reduced variety over a field](../schemes-and-morphisms/varieties-over-a-field/is-variety.md),
  for the underlying variety of the algebraic form, which it takes smooth, projective and integral

## Proof depends on

- [L² estimates for the ∂̄ operator](l2-estimates-for-the-dbar-operator.md), for the Serre–Siegel lemma,
  the holomorphic Morse inequalities, their Corollary 8.4 and the Riemann–Roch formula, in the Kähler nef
  case
- [Kodaira vanishing theorem](kodaira-vanishing-theorem.md), in Esnault–Viehweg's proof of Lemma 5.8 b)
- [Standard results of coherent cohomology on projective varieties](standard-results-of-coherent-cohomology.md),
  for the Hirzebruch–Riemann–Roch theorem, hyperplane sections and Seshadri's criterion (Esnault–Viehweg,
  Lemmas 5.7 and 5.8)

## Sources

- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: Lemma (6.13)
  (c) and the remark after it, p. 45; Lemma (6.18) and Corollary (6.19), p. 48; (8.2) and
  Corollaries (8.3), (8.4), pp. 62–63. The remark after (6.13) cites "Corollary 8.3" for the bound
  $h^q(X, kL) = o(k^n)$, which is Corollary (8.4) in this version.
- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Lemma 5.7, p. 46, and Lemma 5.8 with its proof, pp.
  46–47.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: Lemma 2.1, p. 10.
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the algebraic form over an algebraically closed field, together with the non-negativity of
  intersection numbers of nef line bundles and the estimate $h^0(X, L^m) = \frac{(L^n)}{n!} m^n +
  O(m^{n-1})$ for nef $L$, as `GlobalTheory.Published.NefNumerics`.
