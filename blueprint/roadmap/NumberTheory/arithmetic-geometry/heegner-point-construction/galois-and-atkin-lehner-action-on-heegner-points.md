# Galois and Atkin–Lehner action on Heegner points

Let $N \ge 1$ and let $K$ be an imaginary quadratic field of discriminant $D$, prime to $N$, odd, such that $D$ is a
square modulo $4N$ (so that every prime factor of $N$ splits in $K$), with class number $h$ and Hilbert class field
$H$. A **Heegner point of discriminant $D$** is a point $x = (E \to E')$ of $X_0(N)$, a cyclic $N$-isogeny, such
that $E$ and $E'$ both have complex multiplication by $\mathcal{O}_K$. Let $s$ be the number of distinct prime
factors of $N$ and $W \cong (\mathbb{Z}/2\mathbb{Z})^s$ the group of Atkin–Lehner involutions $w_d$ of $X_0(N)$,
$d \mid N$ with $(d, N/d) = 1$. Then there are exactly $2^s h$ Heegner points of discriminant $D$, all rational over
$H$, and the group $W \times \operatorname{Gal}(H/K)$ permutes them simply transitively.

For a discriminant of either parity, the consequence that the Heegner point needs is
[its independence of the ideal](independence-of-the-heegner-point-from-the-ideal.md).

## Expansion

This node is still to be broken down. A good expansion states and links:

- the count of Heegner points: the pairs $(\mathfrak{a}, \mathfrak{n})$ of a class $\mathfrak{a}$ in the class group and
  an ideal $\mathfrak{n}$ with $\mathcal{O}_K/\mathfrak{n} \cong \mathbb{Z}/N\mathbb{Z}$, giving the isogenies
  $\mathbb{C}/\mathfrak{a} \to \mathbb{C}/\mathfrak{a}\mathfrak{n}^{-1}$;
- the action of $\operatorname{Gal}(H/K)$ through the class group by complex multiplication (Darmon, Theorem 3.7, the
  Shimura reciprocity law) and of $w_d$ by changing $\mathfrak{n}$ at the primes dividing $d$ (Gross and Zagier,
  Chapter I, (2.2)).

## Depends on

- [Complex points of $X_0(N)$ as cyclic $N$-isogenies](complex-points-of-x0-n-as-cyclic-isogenies.md), for the points of $X_0(N)$ as cyclic $N$-isogenies
- [Hilbert class field of a number field](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/is-hilbert-class-field.md), for $H$

## Proof depends on

- [Decomposition of rational primes in a quadratic field](../../algebraic-number-theory/quadratic-fields/quadratic-field-prime-decomposition.md), for the splitting of the prime factors of $N$ when $D$ is a square modulo $4N$ (at $2$, an odd discriminant that is a square modulo $8$ is $1$ modulo $8$)
- [Heegner points are rational over the Hilbert class field](rationality-of-heegner-points.md), for the rationality over $H$
- [Main theorem of complex multiplication for elliptic curves](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/main-theorem-of-complex-multiplication.md), for the Galois action on the CM curves and their torsion

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320: Chapter I, §2, (2.2) and the paragraph after it, p. 227 (the involutions $w_d$ and the group
  $W \cong (\mathbb{Z}/2\mathbb{Z})^s$), and §3, p. 227 ("there are $2^s \cdot h$ Heegner points on $X$, all rational
  over the Hilbert class field $H = K(j(E))$ of $K$. They are permuted simply-transitively by the abelian group
  $W \times \operatorname{Gal}(H/K)$."), under the standing assumptions of §3 ($D$ prime to $N$, odd, a square modulo $4N$).
- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Theorem 3.7 (Shimura reciprocity law), p. 34.
