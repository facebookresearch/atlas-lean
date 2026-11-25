# Weil's theorems on characters of the second degree

This node is still to be broken down. It covers the two results of Weil's 1964 paper on the Weil index of a character
of the second degree that the explicit formulas for the Weil representation and the product formula for Weil indices
use. Let $G$ be a locally compact abelian group with [Pontryagin dual](pontryagin-duality-and-self-duality-of-local-fields.md) $G^*$, written additively with
pairing $\langle x, x^* \rangle$, and $f \colon G \to \mathbb{C}^1$ a character of the second degree: a continuous function with
$f(x + y) = f(x) f(y) \langle x, y\rho \rangle$ for a continuous homomorphism $\rho \colon G \to G^*$, the associated symmetric morphism.

- **Weil index** (Weil, §14, Théorème 2). Fix a Haar measure $dx$ on $G$, the dual measure on $G^*$, and the Fourier
  transform $\mathcal{F}\Phi(x^*) = \int_G \Phi(x) \langle x, x^* \rangle \, dx$, with the positive pairing. Suppose $\rho$ is an isomorphism, with
  module $\lvert \rho \rvert$ for these measures, defined by $\int_{G^*} h(x^*) \, dx^* = \lvert \rho \rvert \int_G h(x\rho) \, dx$, and let $g(x^*) = f(x^* \rho^{-1})^{-1}$. For continuous compactly supported $\Phi$ let
  $(\Phi * f)(x) = \int_G \Phi(u) f(x - u) \, du$. Then $\Phi \mapsto \Phi * f$ is continuous for the $L^2$ norm and extends by
  continuity to $L^2(G)$, and there is a constant $\gamma(f)$ of absolute value $1$, the Weil index of $f$, with
  $\mathcal{F}(\Phi * f) = \gamma(f) \lvert \rho \rvert^{-1/2} \mathcal{F}(\Phi) \cdot g$ for every $\Phi \in L^2(G)$. Weil expresses this by saying that
  $\gamma(f) \lvert \rho \rvert^{-1/2} g$ is the Fourier transform of $f$; since $\lvert f \rvert = 1$, $f$ itself is not in $L^2(G)$ unless $G$ is
  compact.
- **Pointwise forms** (Weil, §14, Corollaires 1 and 2). For $\Phi$ in the Schwartz–Bruhat space $\mathcal{S}(G)$ and every
  $x^* \in G^*$, $\int_G (\Phi * f)(x) \langle x, x^* \rangle \, dx = \gamma(f) \lvert \rho \rvert^{-1/2} \mathcal{F}(\Phi)(x^*) f(x^* \rho^{-1})^{-1}$. In
  particular, at $x^* = 0$, $\int_G \Big( \int_G \Phi(x - y) f(y) \, dy \Big) dx = \gamma(f) \lvert \rho \rvert^{-1/2} \int_G \Phi(x) \, dx$, an iterated
  integral whose inner integral is $(\Phi * f)(x)$.
- **Triviality** (Weil, §20, Théorème 5). Let $\Gamma$ be a closed subgroup of $G$ on which $f$ takes the value $1$, and
  $\Gamma_*$ the subgroup of $G^*$ orthogonal to $\Gamma$. If $\rho$ maps $G$ isomorphically onto $G^*$ and $\Gamma$ onto $\Gamma_*$, then
  $\gamma(f) = 1$.

## Expansion

A good expansion has definition pages for characters of the second degree and their symmetric morphisms, and statement
pages for Théorème 2 with its Corollaires 1 and 2 and for Théorème 5, each citing the source below with locators.

- Every automorphism of the Heisenberg group of $G \times G^*$ that fixes its central circle, the group $B_0(G)$ of Weil's §6,
  whose elements are the pairs $s = (\sigma, h)$ of an automorphism $\sigma$ of $G \times G^*$ and a character of the second degree
  $h$ of $G \times G^*$ acting by $(w, t) \mapsto (w\sigma, h(w) t)$, is
  implemented on $L^2(G)$ by a unitary operator unique up to a scalar of absolute value $1$ (Weil, §§8–10, after Segal), by
  the uniqueness of the irreducible representation on which the centre acts tautologically. Weil obtains $\gamma(f)$ as the
  scalar by which two chosen implementations of the two sides of a relation in $B_0(G)$ differ (his relation (9), §7).
- Under the hypotheses of Théorème 5 all the factors of that relation lie in the subgroup $B_0(G, \Gamma)$ of the elements
  $s = (\sigma, h)$ for which $\sigma$ induces an automorphism of $\Gamma \times \Gamma_*$, preserving it as a set, and $h$ takes the value $1$
  on it (§19, p. 167). It is $h$, not $\sigma$, that is trivial there: for $G = \mathbb{R}$ and $\Gamma = \mathbb{Z}$, the automorphism $-1$ of $\mathbb{R} \times \mathbb{R}$ preserves $\mathbb{Z} \times \mathbb{Z}$
  without fixing it pointwise. There the chosen implementations
  agree with those given by the representation $r_\Gamma$ of $B_0(G, \Gamma)$ (§20), and $r_\Gamma$ respects the relation, so the
  scalar is $1$.
- Applied to an adelic group and its rational points, Théorème 5 gives the global value $\gamma(f) = 1$; the product formula
  for Weil indices (§30) also needs Corollaire 2, applied to a factorizable Schwartz–Bruhat function and to its local
  factors, which factors that value into the local indices.

## Depends on

- [Pontryagin duality and the self-duality of local fields](pontryagin-duality-and-self-duality-of-local-fields.md), for the dual group $G^*$ and the duality pairing

## Proof depends on

- [Induction and Mackey theory for Heisenberg groups](../../RepresentationTheory/automorphic-representations/theta-correspondence/induction-and-mackey-theory-for-heisenberg-groups.md), for the Stone–von Neumann–Mackey theorem for the Heisenberg group of an arbitrary locally compact abelian group: uniqueness of the irreducible unitary representation on which the circle acts tautologically, by which every automorphism fixing the centre is implemented by a unitary operator, unique up to a scalar

## Sources

- A. Weil, "Sur certains groupes d'opérateurs unitaires", Acta Math. 111 (1964), 143–211: §14, Théorème 2 and
  Corollaires 1 and 2, pp. 161–162 (the Fourier transform of a nondegenerate character of the second degree and the
  Weil index $\gamma(f)$, in the $L^2$ sense of the paragraph after Théorème 2, the module of $\rho$ and the dual measures as in §2, and the identities of continuous functions of
  Corollaires 1 and 2 for $\Phi \in \mathcal{S}(G)$), §§8–10 (implementation of the automorphisms in $B_0(G)$), §19, p. 167
  ($B_0(G, \Gamma)$), §20, Théorème 5, p. 169 (with the comparison of the liftings $r_0$ and $r_\Gamma$ on p. 169 that proves it), and §30, the proof of Proposition 5, p. 179 (Corollaire 2 applied to an adelic
  Schwartz–Bruhat function and to its local factors).
