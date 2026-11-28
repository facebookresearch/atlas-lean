# Rosati metric on lattices of homomorphisms

Let $K$ be a field of characteristic zero and let $A$ and $B$ be
[abelian varieties](../abelian-scheme.md) over $K$ with [polarizations](../polarization.md)
$\lambda_A \colon A \to \widehat A$ and $\lambda_B \colon B \to \widehat B$ defined over $K$, where
$\widehat A$ and $\widehat B$ are the [dual abelian varieties](../dual-abelian-variety.md); over an
algebraic closure $\bar K$ of $K$, $\lambda_A = \phi_L$ and $\lambda_B = \phi_M$ for ample invertible
sheaves $L$ on $A_{\bar K}$ and $M$ on $B_{\bar K}$. Write $\operatorname{Hom}_K(A, B)$ for the group
of homomorphisms $A \to B$ defined over $K$, a free $\mathbb{Z}$-module of finite rank,
$\operatorname{End}_K(X) = \operatorname{Hom}_K(X, X)$, and $\widehat\varphi \colon \widehat B \to
\widehat A$ for the dual of $\varphi \in \operatorname{Hom}_K(A, B)$. The degree $\deg \varphi$ of a
homomorphism is the order of its kernel if it is an [isogeny](../isogenies-of-abelian-schemes.md),
and $0$ otherwise; for an abelian variety $X$ over $K$ it extends to a homogeneous polynomial
function of degree $2 \dim X$ on $\operatorname{End}_K(X) \otimes \mathbb{R}$.

1. **Trace.** For an abelian variety $X$ over $K$ and $\varphi \in \operatorname{End}_K(X) \otimes
   \mathbb{R}$, the trace $\operatorname{Tr}(\varphi)$ is the opposite of the coefficient of
   $T^{2 \dim X - 1}$ in the polynomial $\deg(T \operatorname{id}_X - \varphi)$.
2. **Generalized Rosati involution.** For $\varphi \in \operatorname{Hom}_K(A, B) \otimes
   \mathbb{Q}$, put $\varphi^\dagger = \lambda_A^{-1} \circ \widehat\varphi \circ \lambda_B \in
   \operatorname{Hom}_K(B, A) \otimes \mathbb{Q}$. When $(A, \lambda_A) = (B, \lambda_B)$ this is the
   Rosati involution of $\operatorname{End}_K(A) \otimes \mathbb{Q}$; when $\lambda_A$ is principal,
   $\varphi^\dagger \in \operatorname{Hom}_K(B, A)$ for $\varphi \in \operatorname{Hom}_K(A, B)$.
3. **Rosati metric.** Extended $\mathbb{R}$-linearly, the form $\langle \varphi, \psi \rangle =
   \operatorname{Tr}(\varphi \circ \psi^\dagger)$, where $\varphi \circ \psi^\dagger$ is an
   endomorphism of $B$ and its trace is that of item 1 for $X = B$, with $2 \dim B$, is symmetric
   and positive definite on $\operatorname{Hom}_K(A, B) \otimes \mathbb{R}$. The Rosati metric is
   the Euclidean norm $|\varphi| = \operatorname{Tr}(\varphi \circ \varphi^\dagger)^{1/2}$; it makes
   $\operatorname{Hom}_K(A, B)$ a lattice in the Euclidean space $\operatorname{Hom}_K(A, B) \otimes
   \mathbb{R}$. It depends on $A$, $B$ and the two polarizations.
4. **Minima and covolume.** For a lattice $\Gamma$ of rank $n$ in a Euclidean space,
   $\Lambda(\Gamma)$ is the least real number $\lambda \ge 0$ such that $\Gamma$ contains $n$
   linearly independent elements of norm at most $\lambda$ (its last successive minimum), and
   $\operatorname{vol}(\Gamma)$ is its covolume. For $n \ge 1$, $\lambda(\Gamma)$ is the least norm
   of a nonzero element of $\Gamma$, and $\Lambda(\Gamma) > 0$ agrees with Gaudron and Rémond's
   definition (§3, p. 2069). For the zero lattice, $n = 0$ and $\Lambda(0) = 0$; this case occurs,
   for instance $\operatorname{Hom}_K(A, B) = 0$ for non-isogenous elliptic curves $A$ and $B$. With
   the Rosati metric, $\Lambda(\operatorname{Hom}_K(A, B))$ is the last minimum of the lattice of
   homomorphisms.

Gaudron and Rémond write $\varphi^\dagger = \phi_L^{-1} \circ \widehat\varphi \circ \phi_M$ for
polarized abelian varieties $(A, L)$ and $(B, M)$, and note that the Rosati involution and the
degree depend only on the polarization, the one difficulty being the field of definition, as a
polarization defined over a field may be of the form $\phi_L$ only over an extension (p. 2064).
Items 2 and 3 are stated here for the polarizations themselves, which is how the principal
polarizations given by Zarhin's trick enter the isogeny estimate.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the finiteness and freeness of $\operatorname{Hom}_K(A, B)$ and the polynomiality of the degree
  (Mumford, Theorem 3, p. 176, and Theorem 2, p. 174, as cited by Gaudron and Rémond,
  pp. 2062–2063);
- the properties of the trace, integrality on $\operatorname{End}_K(X)$ included (their Propriétés
  2.2, p. 2063, after Mumford, Theorem 4, p. 180);
- the positivity of the Rosati involution, which gives the positive definiteness of the quadratic
  form on $\operatorname{End}_K(A \times B) \otimes \mathbb{R}$ (Mumford, p. 192, as cited on
  p. 2065), after extension of scalars to $\bar K$, where the polarizations come from ample sheaves;
- the orthogonal decomposition of that form along $\operatorname{End}_K(A \times B) =
  \operatorname{End}_K(A) \oplus \operatorname{Hom}_K(B, A) \oplus \operatorname{Hom}_K(A, B) \oplus
  \operatorname{End}_K(B)$ (their Proposition 2.5, p. 2065), which identifies $\varphi^\dagger$ with
  the Rosati involution of $A \times B$ for the product polarization (pp. 2064–2065) and gives the
  positive definiteness on $\operatorname{Hom}_K(A, B) \otimes \mathbb{R}$.

## Depends on

- [Abelian scheme](../abelian-scheme.md), for abelian varieties over $K$
- [Dual abelian variety](../dual-abelian-variety.md), for $\widehat A$, $\phi_L$ and dual homomorphisms
- [Polarization](../polarization.md)
- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for isogenies and their degree

## Sources

- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: §2, pp. 2062–2066 (the degree, Définition 2.1 of the
  trace and Propriétés 2.2, p. 2063; Définition 2.4 of the generalized Rosati involution and the
  remark that it depends only on the polarization, p. 2064; Proposition 2.5 and Définition 2.6 of
  the Rosati metric, p. 2065), and §3, p. 2069 ($\lambda$, $\Lambda$ and $\operatorname{vol}$).
- D. Mumford, *Abelian Varieties*, Oxford University Press, 1974: Theorems 2, 3 and 4,
  pp. 174–180, and p. 192, as cited by Gaudron and Rémond, pp. 2062–2065 (not read).
