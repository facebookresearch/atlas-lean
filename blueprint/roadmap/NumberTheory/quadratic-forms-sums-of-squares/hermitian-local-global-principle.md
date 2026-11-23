# Local–global principle for Hermitian spaces over a quadratic extension

Let $E/K$ be a quadratic extension of number fields with nontrivial automorphism $x \mapsto \bar{x}$. A
Hermitian space over $E$ is a finite-dimensional $E$-vector space $V$ with a map
$\Phi \colon V \times V \to E$ that is additive in each variable and satisfies
$\Phi(\alpha x, \beta y) = \alpha \, \Phi(x, y) \, \bar{\beta}$ and $\Phi(y, x) = \overline{\Phi(x, y)}$;
it is regular if $\Phi(x, V) \neq 0$ for every nonzero $x$. For a place $v$ of $K$ the completion
$V_v = V \otimes_K K_v$ is a Hermitian space over $E_v = E \otimes_K K_v$. Then two regular Hermitian
spaces $(V, \Phi)$ and $(V', \Phi')$ over $E$ are isometric if and only if $(V_v, \Phi)$ and
$(V'_v, \Phi')$ are isometric for every place $v$ of $K$.

Every regular Hermitian space has an orthogonal basis, so it is a diagonal form
$\langle a_1, \dots, a_m \rangle$ with $a_i \in K^\times$ (Kirschmer, Theorem 2.1.4); its determinant
$\det(V, \Phi)$ is the class of $a_1 \cdots a_m$, or of the determinant of any Gram matrix, in
$K^\times / N_{E/K}(E^\times)$. With the local classification, the principle says that two regular
Hermitian spaces over $E$ are isometric exactly when they have the same rank, the same determinant in
$K^\times / N_{E/K}(E^\times)$, and, at each real place $v$ of $K$ at which $E_v \cong \mathbb{C}$, the
same number of negative entries in a diagonal form (Kirschmer, Remark 3.4.2(3)). Indeed, over a
non-archimedean completion where $E_v$ is a field, a regular space is determined by its rank and its
determinant in $K_v^\times / N(E_v^\times)$ (Kirschmer, Theorem 3.2.3), where $E_v$ splits every
regular space of a given rank is isometric to $\langle 1, \dots, 1 \rangle$, and at a real place with
$E_v \cong \mathbb{C}$ Sylvester's law of inertia applies (Kirschmer, Proposition 2.1.5); and, as
Kirschmer notes, by the Hasse norm theorem the global determinant is determined by the set of places
at which it is not a local norm.

For spaces of rank one the principle is exactly the Hasse norm theorem for the quadratic, hence cyclic,
extension $E/K$: $\langle a \rangle \cong \langle a' \rangle$ if and only if
$a'/a \in N_{E/K}(E^\times)$, and locally if and only if $a'/a$ is a local norm. Kirschmer credits the
principle to H. Minkowski, H. Hasse, W. Landherr, M. Kneser and T. Springer and refers to Scharlau's
*Quadratic and Hermitian forms*, Chapter 10, for a proof.

## Proof depends on

- [Hasse norm theorem for cyclic extensions](../algebraic-number-theory/adeles-class-field-theory/hasse-norm-theorem.md)

## Sources

- M. Kirschmer, *Definite quadratic and hermitian forms with small class number*, Habilitationsschrift,
  RWTH Aachen University (2016), <http://www.math.rwth-aachen.de/~Markus.Kirschmer/papers/herm.pdf>:
  Theorem 2.4.1 (Local-Global Principle), Definitions 2.1.1–2.1.3, Theorem 2.1.4, Proposition 2.1.5,
  Theorem 3.2.3 and Remark 3.4.2(3).
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, stated for Gram matrices, as
  `GlobalTheory.Published.HermitianHassePrinciple`, proved as
  `GlobalTheory.Published.hermitianHassePrinciple_holds` with the quadratic case of the Hasse norm
  theorem.
