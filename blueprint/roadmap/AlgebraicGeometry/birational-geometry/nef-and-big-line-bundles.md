# Nef and big line bundles

Let $X$ be a projective variety over a field and $L$ an invertible sheaf on $X$. If
$H^0(X, L^\nu) \ne 0$ for some $\nu \ge 1$, the sections of $L^\nu$ define a rational map
$\varphi_\nu \colon X \dashrightarrow \mathbb{P}(H^0(X, L^\nu))$. The *Iitaka dimension* of $L$ is
$\kappa(L) = -\infty$ if $H^0(X, L^\nu) = 0$ for all $\nu \ge 1$, and otherwise

$$\kappa(L) = \max\{\dim \varphi_\nu(X) : \nu \ge 1,\ H^0(X, L^\nu) \ne 0\};$$

it lies in $\{-\infty, 0, 1, \dots, \dim X\}$. The sheaf $L$ is *big* if $\kappa(L) = \dim X$, and
*nef* (numerically effective) if $\deg(L|_C) \ge 0$ for every irreducible curve $C \subset X$, that is,
if the intersection number $(L \cdot C)$ is non-negative for every such curve. A divisor $B$ is called
nef or big if $\mathcal{O}_X(B)$ is. Lazarsfeld extends both notions "in the evident manner" to
$\mathbb{Q}$-divisors $D$ on a smooth projective variety: $D$ is nef if $(D \cdot C) \ge 0$ for every
irreducible curve $C$, the intersection number being extended $\mathbb{Q}$-linearly, and big if some
positive multiple of $D$ is an integral big divisor.

Bigness is maximal growth of the spaces of sections, which is how Lazarsfeld phrases it
($h^0(X, \mathcal{O}_X(mB))$ grows like $m^{\dim X}$): if $H^0(X, L^\nu) \ne 0$ for some $\nu \ge 1$,
there are real numbers $a, b > 0$ with

$$a\,\mu^{\kappa(L)} \le \dim H^0(X, L^{\nu\mu}) \le b\,\mu^{\kappa(L)} \qquad (\mu \ge 1)$$

(Esnault–Viehweg, Properties 5.4 b)). Moreover $\kappa(L) = \dim X$ if and only if $L^\nu(-C)$ is ample
for some $\nu \ge 1$ and some effective divisor $C$ (Properties 5.4 d)).

**Analytic definitions.** Let $X$ be a compact complex manifold with a hermitian metric $\omega$ and $L$
a holomorphic line bundle on $X$. Demailly calls $L$ nef if for every $\varepsilon > 0$ there is a
smooth hermitian metric $h_\varepsilon$ on $L$ whose curvature satisfies
$i\Theta_{L,h_\varepsilon} \ge -\varepsilon\omega$ (Definition 6.11). He defines the Kodaira–Iitaka
dimension $\kappa(L)$ as the supremum over $m \ge 1$ of the ranks of the maps

$$\Phi_m \colon X \setminus B_m \to \mathbb{P}(V_m), \qquad x \mapsto \{\sigma \in V_m : \sigma(x) = 0\},$$

where $V_m = H^0(X, mL)$ and $B_m = \bigcap_{\sigma \in V_m} \sigma^{-1}(0)$ is its base locus, with
$\kappa(L) = -\infty$ if $V_m = 0$ for all $m \ge 1$; $L$ is big if $\kappa(L) = \dim X$
(Definition 6.12). On a projective manifold carrying an ample line bundle $A$, the following are
equivalent: $L$ is nef in the sense of curves; $kL + A$ is ample for every integer $k \ge 1$; $L$ is
nef in the analytic sense, a condition that does not depend on $\omega$ (Proposition 6.10).

## Sources

- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Definition 5.3 (Iitaka dimension) and Properties 5.4 a),
  b), d), p. 44; Definition 5.5 b) (numerically effective sheaves), p. 45.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: the opening of §2, p. 10 (nef and big divisors and their
  extension to $\mathbb{Q}$-divisors).
- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: Definition
  (6.9), p. 43; Proposition (6.10), Definitions (6.11) and (6.12), p. 44.
