# Heegner points are rational over the Hilbert class field

Let $K \subset \mathbb{C}$ be an imaginary quadratic field and $N \ge 1$ an integer whose prime factors all split in
$K$, let $\mathcal{N}$ be an ideal of $\mathcal{O}_K$ with $\mathcal{O}_K/\mathcal{N}$ cyclic of order $N$, and let
$x_1 \in X_0(N)(\mathbb{C})$ be the point of the cyclic $N$-isogeny
$\mathbb{C}/\mathcal{O}_K \to \mathbb{C}/\mathcal{N}^{-1}$ ([complex points of $X_0(N)$](complex-points-of-x0-n-as-cyclic-isogenies.md)).
Let $K_1 \subset \mathbb{C}$ be the [Hilbert class field](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/is-hilbert-class-field.md)
of $K$. Then $x_1$ is a point of $X_0(N)(K_1)$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the plane model of $X_0(N)$ over $\mathbb{Q}$ in the coordinates $(j(\tau), j(N\tau))$, cut out by the $N$-th modular
  polynomial, and its relation to the standard model of the modular curve page (Darmon, p. 18);
- the coordinates of $x_1$ in that model, $j(\mathcal{O}_K)$ and $j(\mathcal{N}^{-1})$, which lie in $K_1$ because both
  lattices have endomorphism ring $\mathcal{O}_K$ (the pages linked under Proof depends on), and the passage from
  the plane model to the curve (Darmon, proof of Theorem 3.6).

## Depends on

- [Complex points of $X_0(N)$ as cyclic $N$-isogenies](complex-points-of-x0-n-as-cyclic-isogenies.md), for $x_1$
- [Hilbert class field of a number field](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/is-hilbert-class-field.md), for $K_1$

## Proof depends on

- [The $j$-invariant of a CM lattice generates the Hilbert class field](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/hilbert-class-field-generated-by-j.md), for $j(\mathcal{O}_K) \in K_1$
- [Artin symbols act on the $j$-invariants of CM lattices](../../algebraic-number-theory/adeles-class-field-theory/hilbert-class-field/artin-action-on-cm-j-invariants.md), for $j(\mathfrak{a}) \in K_1$ for every fractional ideal $\mathfrak{a}$, in particular $\mathfrak{a} = \mathcal{N}^{-1}$

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: Theorem 3.5 and Theorem 3.6 with its proof, p. 33 ("By Theorem 3.5, both $j(\tau)$ and $j(N\tau)$ belong to a
  ring class field $H$ of $K$ associated to the order $\mathcal{O}_\tau \cap \mathcal{O}_{N\tau}$."); the plane model, p. 18.
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: §1, p. 235 ("The theory of complex multiplication shows that the point $x_1$ is rational over $K_1$, the
  Hilbert class field of $K$.").
- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320: Chapter I, §3, p. 227 (Heegner points are "all rational over the Hilbert class field $H = K(j(E))$ of $K$").
