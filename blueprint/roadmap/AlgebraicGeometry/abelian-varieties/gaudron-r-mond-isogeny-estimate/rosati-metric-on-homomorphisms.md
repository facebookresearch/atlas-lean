# Rosati metric on lattices of homomorphisms

Let $K$ be a field of characteristic zero and let $A$ and $B$ be
[abelian varieties](../abelian-scheme.md) over $K$, with $g = \dim A$, carrying
[polarizations](../polarization.md) $\phi_L \colon A \to \widehat A$ and $\phi_M \colon B \to
\widehat B$ attached to ample invertible sheaves $L$ on $A$ and $M$ on $B$, where $\widehat A$ and
$\widehat B$ are the [dual abelian varieties](../dual-abelian-variety.md). Write
$\operatorname{Hom}_K(A, B)$ for the group of homomorphisms $A \to B$ defined over $K$, a free
$\mathbb{Z}$-module of finite rank, $\operatorname{End}_K(A) = \operatorname{Hom}_K(A, A)$, and
$\widehat\varphi \colon \widehat B \to \widehat A$ for the dual of $\varphi \in
\operatorname{Hom}_K(A, B)$. The degree $\deg \varphi$ of a homomorphism is the order of its kernel
if it is an [isogeny](../isogenies-of-abelian-schemes.md), and $0$ otherwise; it extends to a
homogeneous polynomial function of degree $2g$ on $\operatorname{End}_K(A) \otimes \mathbb{R}$.

1. **Trace.** For $\varphi \in \operatorname{End}_K(A) \otimes \mathbb{R}$, the trace
   $\operatorname{Tr}(\varphi)$ is the opposite of the coefficient of $X^{2g-1}$ in the polynomial
   $\deg(X \operatorname{id}_A - \varphi)$.
2. **Generalized Rosati involution.** For $\varphi \in \operatorname{Hom}_K(A, B) \otimes
   \mathbb{Q}$, put $\varphi^\dagger = \phi_L^{-1} \circ \widehat\varphi \circ \phi_M \in
   \operatorname{Hom}_K(B, A) \otimes \mathbb{Q}$. When $A = B$ and $L = M$ this is the Rosati
   involution of $\operatorname{End}_K(A) \otimes \mathbb{Q}$; when $L$ is principal,
   $\varphi^\dagger \in \operatorname{Hom}_K(B, A)$ for $\varphi \in \operatorname{Hom}_K(A, B)$.
3. **Rosati metric.** Extended $\mathbb{R}$-linearly, the form $\langle \varphi, \psi \rangle =
   \operatorname{Tr}(\varphi \circ \psi^\dagger)$, the trace of an endomorphism of $B$, is symmetric
   and positive definite on $\operatorname{Hom}_K(A, B) \otimes \mathbb{R}$. The Rosati metric is
   the Euclidean norm $|\varphi| = \operatorname{Tr}(\varphi \circ \varphi^\dagger)^{1/2}$; it makes
   $\operatorname{Hom}_K(A, B)$ a lattice in the Euclidean space $\operatorname{Hom}_K(A, B) \otimes
   \mathbb{R}$. It depends on $A$, $B$ and the two polarizations.
4. **Minima and covolume.** For a lattice $\Gamma$ of rank $n$ in a Euclidean space, $\lambda(\Gamma)$
   is the least norm of a nonzero element of $\Gamma$, $\Lambda(\Gamma)$ is the least real number
   $\lambda > 0$ such that $\Gamma$ contains $n$ linearly independent elements of norm at most
   $\lambda$ (its last successive minimum), and $\operatorname{vol}(\Gamma)$ is its covolume. With
   the Rosati metric, $\Lambda(\operatorname{Hom}_K(A, B))$ is the last minimum of the lattice of
   homomorphisms.

## Expansion

A good expansion has pages for: the finiteness and freeness of $\operatorname{Hom}_K(A, B)$ and the
polynomiality of the degree (Mumford, Theorem 3, p. 176, and Theorem 2, p. 174, as cited by
Gaudron and Rémond, pp. 2062–2063); the properties of the trace, integrality on $\operatorname{End}_K(A)$ included
(their Propriétés 2.2, after Mumford, Theorem 4, p. 180); the positivity of the Rosati involution,
which gives the positive definiteness of the quadratic form on $\operatorname{End}_K(A \times B)
\otimes \mathbb{R}$ (Mumford, p. 192, as cited on p. 2065); and the orthogonal decomposition of that
form along $\operatorname{End}_K(A \times B) = \operatorname{End}_K(A) \oplus
\operatorname{Hom}_K(B, A) \oplus \operatorname{Hom}_K(A, B) \oplus \operatorname{End}_K(B)$
(their Proposition 2.5), which identifies $\varphi^\dagger$ with the Rosati involution of $A \times
B$ for the product polarization and gives the positive definiteness on $\operatorname{Hom}_K(A, B)
\otimes \mathbb{R}$.

## Depends on

- [Abelian scheme](../abelian-scheme.md), for abelian varieties over $K$
- [Dual abelian variety](../dual-abelian-variety.md), for $\widehat A$, $\phi_L$ and dual homomorphisms
- [Polarization](../polarization.md)
- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for isogenies and their degree

## Sources

- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: §2, pp. 2062–2066 (the degree, Définition 2.1 of the
  trace, p. 2063; Définition 2.4 of the generalized Rosati involution, p. 2064; Proposition 2.5 and
  Définition 2.6 of the Rosati metric, p. 2065), and §3, p. 2069 ($\lambda$, $\Lambda$ and
  $\operatorname{vol}$).
- D. Mumford, *Abelian Varieties*, Oxford University Press, 1974: Theorems 2, 3 and 4,
  pp. 174–180, and p. 192, as cited by Gaudron and Rémond, pp. 2062–2065 (not read).
