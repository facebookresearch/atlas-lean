# Quadratic twists with nonvanishing central value

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$ with $L$-function
$L(E, s) = \sum_{n \ge 1} a_n n^{-s}$, and suppose that its root number $w(E)$, the sign in the functional equation
of [the $L$-function of an elliptic curve](functional-equation-of-the-l-function-of-an-elliptic-curve.md), is $-1$.
For a negative fundamental discriminant $D$ (a
[fundamental imaginary quadratic discriminant](../algebraic-number-theory/quadratic-fields/imaginary-quadratic-discriminants/is-fundamental-imaginary-quadratic-discr.md))
prime to $N$, let $\varepsilon_D$ be the
[quadratic Dirichlet character](../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md)
of $D$, the primitive character modulo $\lvert D \rvert$ given by the Kronecker symbol
$n \mapsto \left(\frac{D}{n}\right)$, which is the character of the
[imaginary quadratic field](../quadratic-forms-sums-of-squares/binary-quaternary-forms/binary-quadratic-forms/imaginary-quadratic-field.md)
$K = \mathbb{Q}(\sqrt{D}) = \mathbb{Q}(i\sqrt{\lvert D \rvert})$; then $\varepsilon_D(-1) = -1$. Let
$L(E, \varepsilon_D, s) = \sum_{n \ge 1} \varepsilon_D(n) a_n n^{-s}$, which extends to an entire function. Then
there are infinitely many negative fundamental discriminants $D$, prime to $N$, such that

1. $\varepsilon_D(\ell) = 1$ for every prime $\ell$ dividing $N$, that is, every prime factor of $N$ splits in
   $\mathbb{Q}(\sqrt{D})$;
2. $L(E, \varepsilon_D, 1) \ne 0$.

As $D \mapsto \mathbb{Q}(\sqrt{D})$ is a bijection from the negative fundamental discriminants onto the imaginary
quadratic fields, this says, in the form Coates states it: there are infinitely many imaginary quadratic fields $K$, of
discriminant prime to $N$, in which every prime factor of $N$ splits and for which $L(E, \varepsilon_K, 1) \ne 0$,
with $\varepsilon_K$ the character of $K$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the theorem of Waldspurger that gives this, with the local conditions it allows, from the cited sources;
- the analytic continuation of $L(E, \varepsilon_D, s)$, which for $D$ prime to $N$ is the $L$-function of the twist of
  the newform of $E$ by $\varepsilon_D$ and Coates' $L(E^{(\varepsilon)}, s)$ of the twisted curve.

The proof of the rank-one theorem applies the
[Gross–Zagier–Zhang formula](../arithmetic-geometry/gross-zagier-zhang-formula.md) to such a field, with no condition
on the parity of $D$. When $w(E) = 1$ the same proof uses instead the nonvanishing of $L'(E, \varepsilon_D, 1)$
(Bump–Friedberg–Hoffstein, Murty–Murty), which is not part of this page.

## Depends on

- [Fundamental imaginary quadratic discriminant](../algebraic-number-theory/quadratic-fields/imaginary-quadratic-discriminants/is-fundamental-imaginary-quadratic-discr.md), for the discriminants $D$
- [The imaginary quadratic field $\mathbb{Q}(\sqrt{-D})$](../quadratic-forms-sums-of-squares/binary-quaternary-forms/binary-quadratic-forms/imaginary-quadratic-field.md), for $K = \mathbb{Q}(i\sqrt{\lvert D \rvert})$
- [Analytic continuation and functional equation of the $L$-function of an elliptic curve over $\mathbb{Q}$](functional-equation-of-the-l-function-of-an-elliptic-curve.md), for the root number $w(E)$
- [Quadratic Dirichlet character of a fundamental discriminant](../congruences/power-residues-reciprocity/kronecker-symbol-and-quadratic-characters/quadratic-dirichlet-character.md), for $\varepsilon_D$

## Proof depends on

- [Decomposition of rational primes in a quadratic field](../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md), for the equivalence in item 1: a prime $\ell \nmid D$ splits in $\mathbb{Q}(\sqrt{D})$ exactly when $\left(\frac{D}{\ell}\right) = \varepsilon_D(\ell) = 1$

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: the sketch of proof of Theorem 3.22, pp. 40–41 ("Suppose first that
  $\operatorname{sign}(E, \mathbb{Q})$ is equal to $-1$. By a result of [Wa85] (see also [MM97]), there exist
  infinitely many quadratic Dirichlet characters $\varepsilon$ such that (1) $\varepsilon(\ell) = 1$ for all $\ell \mid N$;
  (2) $\varepsilon(-1) = -1$; (3) $L(E, \varepsilon, 1) \ne 0$."), with the remark there that the imaginary quadratic
  field of such an $\varepsilon$ satisfies the Heegner hypothesis (Hypothesis 3.9, p. 35).
- J. Coates, *The work of Gross and Zagier on Heegner points and the derivatives of $L$-series*, Séminaire Bourbaki,
  exp. 635 (1984/85), Astérisque 133–134 (1986), 57–72, <http://www.numdam.org/item?id=SB_1984-1985__27__57_0>:
  pp. 64–65, the definition $L(E^{(\varepsilon)}, s) = \sum a_n \varepsilon(n) n^{-s}$ and the proof of Theorem 5
  ("a deep theorem of Waldspurger [14] proves the existence of (infinitely many) $K$ satisfying the conditions of
  Theorem 4 and such that $L(E^{(\varepsilon)}, 1) \neq 0$"), where the conditions of Theorem 4 (p. 64) are that $K$ is
  imaginary quadratic of discriminant $D$ with $(D, N) = 1$ and every prime factor of $N$ split in $K$.
- R. L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank zero
  and one*, LMS J. Comput. Math. 14 (2011), 327–350, doi:10.1112/S1461157011000180: the proof of Theorem 4.4, p. 336
  ("If $\varepsilon = -1$ (that is, $r_{\mathrm{an}}(E) = 1$), then a result of Waldspurger (see [57]) implies that there
  are infinitely many $D < 0$ such that $K = \mathbb{Q}(\sqrt{D})$ satisfies the Heegner hypothesis for $E$ and
  $r_{\mathrm{an}}(E^D) = 0$."), with $D$ squarefree (§4, p. 335).
- W. Zhang, *The Birch–Swinnerton-Dyer conjecture and Heegner points: a survey*, Current Developments in Mathematics
  2013, International Press, 2014, 169–203: p. 176, after Theorem 1.4 ("Such auxiliary choice exists by a non-vanishing
  result in analytic number theory"), citing Bump–Friedberg–Hoffstein and Murty–Murty.
- J.-L. Waldspurger, *Sur les valeurs de certaines fonctions $L$ automorphes en leur centre de symétrie*, Compositio
  Math. 54 (1985), no. 2, 173–242; M. R. Murty and V. K. Murty, *Non-vanishing of $L$-functions and applications*,
  Progress in Mathematics 157, Birkhäuser, 1997; D. Bump, S. Friedberg and J. Hoffstein, *Eisenstein series on the
  metaplectic group and nonvanishing theorems for automorphic $L$-functions and their derivatives*, Ann. of Math. (2)
  131 (1990), no. 1, 53–127, and *Nonvanishing theorems for $L$-functions of modular forms and their derivatives*,
  Invent. Math. 102 (1990), no. 3, 543–618; M. R. Murty and V. K. Murty, *Mean values of derivatives of modular
  $L$-series*, Ann. of Math. (2) 133 (1991), no. 3, 447–475. Not read here; cited as Darmon (pp. 40–41 and
  bibliography) and Zhang (p. 176 and bibliography) cite them.
