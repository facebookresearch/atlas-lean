# Fricke eigenvalue of a newform

Let $N \ge 1$ and let $f \in S_2(\Gamma_0(N))$ be a newform of level $N$: a simultaneous eigenvector of the Hecke
operators in the new subspace $S_2^{\mathrm{new}}(N)$, the orthogonal complement of the oldforms for the Petersson
product, normalised by $a_1(f) = 1$. Then the [Fricke involution](fricke-involution-on-weight-two-cusp-forms.md)
preserves $S_2^{\mathrm{new}}(N)$ and

$$f \mid_2 W_N = \varepsilon f \qquad \text{for some } \varepsilon = \varepsilon(f) \in \{1, -1\}.$$

Equivalently, the differential $\omega_f = 2\pi i f(z)\,dz$ satisfies $w_N^* \omega_f = \varepsilon \, \omega_f$ for
$w_N(z) = -1/(Nz)$ (a direct computation, worked out here: $f(-1/(Nz)) \, d(-1/(Nz)) = N^{-1} z^{-2} f(-1/(Nz)) \, dz$).

## Expansion

This node is still to be broken down. A good expansion states and links:

- the commutation of $w_N$ with the Hecke operators $T_n$, $(n, N) = 1$, and its preservation of the old and new
  subspaces (Darmon, after (2.12));
- the Atkin–Lehner theorem that the eigenspaces of the Hecke algebra on $S_2^{\mathrm{new}}(N)$ are one-dimensional
  (Darmon, Theorem 2.8 and Corollary 2.9), so that $f \mid_2 W_N$ is a multiple of $f$, with $\varepsilon^2 = 1$ by
  item 3 of the Fricke involution page.

## Depends on

- [The Fricke matrix normalises $\Gamma_0(N)$ and acts on weight-two cusp forms as an involution](fricke-involution-on-weight-two-cusp-forms.md), for $W_N$
- [Hecke operators $T_n$ on weight-two cusp forms for a group of level $N$](../../modular-forms-q-series/modular-forms/hecke-operators-of-level-n.md), for the Hecke operators of which $f$ is an eigenvector

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: §2.3, p. 17 (oldforms, the new subspace, Theorem 2.8 (Atkin–Lehner) and Corollary 2.9, "The simultaneous
  eigenvector $f_\lambda$ is sometimes called a normalised eigenform or simply a newform of level $N$"); (2.12) and
  (2.13), pp. 17–18 ("for any newform $f$ of level $N$, $w_N(f) = \varepsilon f$, where $\varepsilon = \pm 1$"). With the
  printed sign of Darmon's operator (2.12), which is $-(f \mid_2 W_N)$ once its argument is corrected (see the
  [Fricke involution page](fricke-involution-on-weight-two-cusp-forms.md)), $\varepsilon$ would change sign; the
  $\varepsilon$ here is the eigenvalue of $f \mid_2 W_N$, the one for which Darmon's (2.14) holds.
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: (5.2), p. 243 ("$f \mid w_N = \epsilon \cdot f$").
