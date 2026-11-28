# Modular parametrization of an elliptic curve over $\mathbb{Q}$

Let $E$ be an elliptic curve over $\mathbb{Q}$ of conductor $N$, let $f$ be the
newform of weight $2$ and level $N$ with $L(f, s) = L(E, s)$ given by
[modularity of elliptic curves over $\mathbb{Q}$](../../../AlgebraicGeometry/elliptic-curves/modularity-of-elliptic-curves-over-q.md),
and let $X_0(N)$ be the [modular curve](modular-curves-and-hecke-operators-of-level-n/modular-curve-of-a-group-of-level-n.md) $X_\Gamma$ over $\mathbb{Q}$ for
$\Gamma = \Gamma_0(N)$, with its cusp $\infty$, a rational point; Gross and Zagier describe its points as elliptic
curves with a cyclic $N$-isogeny. Then there is a nonconstant morphism

$$\pi \colon X_0(N) \to E$$

defined over $\mathbb{Q}$ with $\pi(\infty) = O$, the origin of $E$. For every such $\pi$ and every Néron differential
$\omega$ of $E$, the pullback $\pi^*(\omega)$ is $c \, \omega_f$ for a nonzero integer $c$, where
$\omega_f = 2\pi i f(z) \, dz = \sum_{n \ge 1} a_n(f) q^n \, dq/q$ is the differential of $f$ on $X_0(N)$.

## Expansion

This node is still to be broken down. A good expansion states and links, following Gross and Zagier's derivation
(their Chapter V, §2, p. 310):

- the strong Weil curve $E_0$ that the Eichler–Shimura construction attaches to $f$, a quotient of the Jacobian of
  $X_0(N)$ over $\mathbb{Q}$ with $L(E_0, s) = L(f, s)$, and the resulting morphism $X_0(N) \to E_0$ sending $\infty$
  to the origin;
- Faltings' isogeny theorem, which gives an isogeny $E_0 \to E$ over $\mathbb{Q}$, as $L(E, s) = L(E_0, s)$; the
  composite is $\pi$;
- the pullback $\pi^*(\omega)$, which lies in the $f$-isotypic part of the differentials of $X_0(N)$, spanned by
  $\omega_f$, so is $c\,\omega_f$ with $c \ne 0$ as $\pi$ is nonconstant; and the integrality of $c$, recorded by the
  sources below, proved or cited with its source.

Darmon (p. 21) gives the same map as a complex uniformisation $\Phi_N$ of $E(\mathbb{C})$ by the upper half-plane.

## Depends on

- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](modular-curves-and-hecke-operators-of-level-n/modular-curve-of-a-group-of-level-n.md), for $X_0(N) = X_{\Gamma_0(N)}$ over $\mathbb{Q}$
- [Modularity of elliptic curves over $\mathbb{Q}$](../../../AlgebraicGeometry/elliptic-curves/modularity-of-elliptic-curves-over-q.md), for the newform $f$

## Proof depends on

- [Abel–Jacobi map](../../../AlgebraicGeometry/algebraic-curves/jacobians-of-curves/of-curve.md), for the map $X_0(N) \to J_0(N)$ based at the cusp $\infty$, $P \mapsto$ the class of $(P) - (\infty)$ (Darmon, p. 19)
- [The Abel–Jacobi map sends the base point to zero](../../../AlgebraicGeometry/algebraic-curves/jacobians-of-curves/comp-of-curve.md), for the image $0$ of $\infty$, so that the composite with the quotient sends $\infty$ to the origin
- [Shimura's abelian variety attached to a weight-two eigenform](shimura-abelian-variety-of-an-eigenform.md), its item (i) for $\Gamma = \Gamma_0(N)$ and $f$: the quotient $\nu \colon J_0(N) \to E_0$ over $\mathbb{Q}$ of the Jacobian of $X_0(N)$ (Darmon, §2.5, pp. 18–19), an elliptic curve by its item (iii) as the $a_n(f)$ are integers, through which $X_0(N) \to E_0$, $P \mapsto \nu((P) - (\infty))$, sends $\infty$ to the origin
- [Modularity of elliptic curves over $\mathbb{Q}$](../../../AlgebraicGeometry/elliptic-curves/modularity-of-elliptic-curves-over-q.md), for $L(E, s) = L(f, s)$ and the isogeny from $E$ to the Eichler–Shimura curve of $f$

The rest of its proof is that of the sources below, as the Expansion describes.

## Sources

- B. H. Gross and D. B. Zagier, *Heegner points and derivatives of $L$-series*, Invent. Math. 84 (1986), 225–320:
  Chapter V, §2, p. 310 ("by Faltings' isogeny theorem any elliptic curve with $L(E, s) = L(f, s)$ is isogenous to
  $E_0$ and hence admits a covering map $\pi \colon X_0(N) \to E$ ($N$ = level of $f$) defined over $\mathbb{Q}$ and
  sending the cusp $\infty$ to $0 \in E(\mathbb{Q})$"; "Then $\pi^*(\omega) = c\,\omega_f$ for some non-zero integer
  $c$").
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: §1, p. 235 (the parametrization
  $\varphi \colon X_0(N) \to E$ mapping $\infty$ to the origin, and "It is known that $c$ is an integer").
- H. Darmon, *Rational points on modular elliptic curves*, CBMS Regional Conference Series in Mathematics 101,
  American Mathematical Society, 2004; author's version,
  <https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf>, cited by the page numbers
  printed in that version: the second corollary of Wiles' theorem, p. 21, and the Eichler–Shimura construction,
  Theorem 2.10 and its sketch of proof, pp. 18–19.
