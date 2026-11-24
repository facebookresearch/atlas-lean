# Analytic elliptic regularity

This node is still to be broken down. It covers the analyticity of solutions of elliptic equations with analytic
coefficients, which the regularity of automorphic forms and Harish-Chandra's analyticity theorem use. Let $X$ be a real
analytic manifold and $D$ a linear differential operator on $X$ with real analytic coefficients. $D$ is elliptic at $x$
if its principal symbol $\sigma(D)_x$, a homogeneous polynomial on $T^*_x X$, vanishes only at $0$, and elliptic if it
is elliptic at every point.

- **Theorem.** If $D$ is elliptic, every distribution $u$ on $X$ with $Du$ real analytic, in particular every
  distributional solution of $Du = 0$, is a real analytic function.
- **Invariant elliptic operators on Lie groups.** Let $G$ be a real [Lie group](../../Geometry/differential-topology/lie-group.md)
  and $K$ a compact subgroup. The Laplace operator of a left-invariant Riemannian metric on $G$ that is also invariant
  under right translations by $K$ is elliptic, has real analytic coefficients and is given by an element of
  $U(\mathfrak{g})^K$. For a Cartan decomposition $\mathfrak{g} = \mathfrak{k} \oplus \mathfrak{p}$ of a semisimple Lie
  algebra, the operator $\Omega = 2 C_{\mathfrak{k}} + C_{\mathfrak{g}}$ built from Casimir operators of $\mathfrak{g}$ and
  $\mathfrak{k}$ is the sum of the squares of a basis of $\mathfrak{g}$ orthonormal for the positive definite form
  $-B(X, \theta Y)$, with $B$ the Killing form and $\theta$ the Cartan involution, hence elliptic.

## Expansion

A good expansion has a definition page for elliptic operators, a statement page for the theorem, first for smooth
solutions of homogeneous equations and then for distributions and analytic right-hand sides, and a statement page for
the invariant elliptic operators on Lie groups, each citing the sources below with locators. Casselman follows the proof
of F. John through plane wave decompositions and the Cauchy–Kovalevskaya theorem; the other classical proof, through
estimates of derivatives, is due to Morrey and Nirenberg.

## Depends on

- [Lie group](../../Geometry/differential-topology/lie-group.md), for the invariant operators on Lie groups

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- P. Etingof, "Representations of Lie groups", lecture notes, arXiv:2401.01446 (version 3): §6.2, Definition 6.4
  (elliptic operators), Theorem 6.6 and Corollary 6.7 (smooth solutions of $Df = 0$ are real analytic) and Remark 6.8 (1)
  (the same for distributional solutions and for $Df = g$ with $g$ analytic), pp. 34–35, and §6.3, p. 36 (a left-invariant,
  $K$-invariant Riemannian metric gives an elliptic Laplace operator in $U(\mathfrak{g})^K$).
- W. Casselman, "Elliptic differential equations—analyticity", Essays in analysis (2012),
  <https://personal.math.ubc.ca/~cass/research/pdf/Analytic.pdf>: Theorem 1.1 (solutions of an elliptic equation with
  analytic coefficients on an open disc are analytic) and §1 (its history: F. John 1955, Morrey and Nirenberg 1957).
- A. Borel, "Automorphic forms on reductive groups", lecture notes (Park City),
  <http://homepages.math.uic.edu/~rtakloo/papers/borel/borel3.pdf>: §4.1, p. 4 (the elliptic operator
  $\Omega = 2 C_{\mathfrak{k}} + C_{\mathfrak{g}}$).
