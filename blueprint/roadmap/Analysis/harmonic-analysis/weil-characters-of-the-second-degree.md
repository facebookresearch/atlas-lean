# Weil's theorems on characters of the second degree

This node is still to be broken down. It covers the two results of Weil's 1964 paper on the Weil index of a character
of the second degree that the explicit formulas for the Weil representation and the product formula for Weil indices
use. Let $G$ be a locally compact abelian group with [Pontryagin dual](pontryagin-duality-and-self-duality-of-local-fields.md) $G^*$, written additively with
pairing $\langle x, x^* \rangle$, and $f \colon G \to \mathbb{C}^1$ a character of the second degree: a continuous function with
$f(x + y) = f(x) f(y) \langle x, y\rho \rangle$ for a continuous homomorphism $\rho \colon G \to G^*$, the associated symmetric morphism.

- **Weil index** (Weil, §14, Théorème 2). If $\rho$ is an isomorphism, $f$ has a Fourier transform in the sense of $L^2(G)$:
  $\mathcal{F}f = \gamma(f) \lvert \rho \rvert^{-1/2} g$, where $g(x^*) = f(x^* \rho^{-1})^{-1}$, $\lvert \rho \rvert$ is the module of $\rho$ for the chosen Haar
  measures and $\gamma(f)$ is a constant of absolute value $1$, the Weil index of $f$. Its Corollaire 2 expresses the integral
  $\int_G \Phi f$, for $\Phi$ in the Schwartz–Bruhat space $\mathcal{S}(G)$, through $\gamma(f)$, $\lvert \rho \rvert$ and the Fourier transform
  of $\Phi$ integrated against $g$.
- **Triviality** (Weil, §20, Théorème 5). Let $\Gamma$ be a closed subgroup of $G$ on which $f$ takes the value $1$, and
  $\Gamma_*$ the subgroup of $G^*$ orthogonal to $\Gamma$. If $\rho$ maps $G$ isomorphically onto $G^*$ and $\Gamma$ onto $\Gamma_*$, then
  $\gamma(f) = 1$.

## Expansion

A good expansion has definition pages for characters of the second degree and their symmetric morphisms, and statement
pages for Théorème 2 with its Corollaire 2 and for Théorème 5, each citing the source below with locators. Weil obtains
$\gamma(f)$ as the scalar by which the lifts to the group $B_0(G)$ of the two sides of a relation in the group of
automorphisms of the Heisenberg group differ (his relation (9)). Under the hypotheses of Théorème 5 all the factors of
that relation preserve $\Gamma$, where these lifts agree with those given by a representation of the stabilizer of
$\Gamma$ (§§18–20), so the scalar is $1$; applied to an adelic group and its rational points, it gives the product formula
for Weil indices (§30).

## Depends on

- [Pontryagin duality and the self-duality of local fields](pontryagin-duality-and-self-duality-of-local-fields.md), for the dual group $G^*$ and the duality pairing

## Proof depends on

- [Stone–von Neumann theorem for Heisenberg groups over local fields](../../RepresentationTheory/automorphic-representations/theta-correspondence/stone-von-neumann-theorem.md), for the uniqueness of the Heisenberg representation, by which the automorphisms of the Heisenberg group act projectively

## Sources

- A. Weil, "Sur certains groupes d'opérateurs unitaires", Acta Math. 111 (1964), 143–211: §14, Théorème 2 and
  Corollaires 1 and 2, pp. 161–162 (the Fourier transform of a nondegenerate character of the second degree and the
  Weil index $\gamma(f)$), and §20, Théorème 5, p. 169 (with the comparison of the liftings $r_0$ and $r_\Gamma$ on p. 169 that proves it).
