# The Jacobian of a compact Riemann surface and the Jacobian variety of a curve

Let $C$ be a curve over $\mathbb{C}$, that is, a proper smooth geometrically irreducible $\mathbb{C}$-scheme of dimension
one, let $J_C$ be its [Jacobian variety](../../jacobians-of-curves/jacobian.md), and let
$P \in C(\mathbb{C})$, with $f^P \colon C \to J_C$ the [Abel–Jacobi map](../../jacobians-of-curves/of-curve.md) based at
$P$, the canonical map sending a point $Q$ to the class of the divisor $Q - P$. Let $X = C(\mathbb{C})$, a compact Riemann surface, with
[Jacobian](../../jacobians-of-compact-riemann-surfaces/jacobian.md) $J(X)$ and
[Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md)
$\varphi_P \colon X \to J(X)$. Then $J_C$ is an abelian variety over $\mathbb{C}$, and there is an isomorphism of
complex Lie groups $J(X) \to J_C(\mathbb{C})$ carrying $\varphi_P$ to $f^P$. In particular $J(X)$ is the complex torus of
a complex abelian variety.

For a group $\Gamma$ of level $N$ and the
[modular curve](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md)
$X_\Gamma$, whose complex points form the compact Riemann surface $\mathfrak{H}^*/\Gamma$, this identifies the Jacobian of
$\mathfrak{H}^*/\Gamma$ with $J(\mathbb{C})$ for the Jacobian $J$ of $X_\Gamma$, through which it is a complex abelian
variety.

## Depends on

- [Jacobian of a smooth proper curve](../../jacobians-of-curves/jacobian.md), for $J_C$
- [Abel–Jacobi map](../../jacobians-of-curves/of-curve.md), for the morphism $f^P \colon C \to J_C$
- [Jacobian of a compact Riemann surface](../../jacobians-of-compact-riemann-surfaces/jacobian.md),
  for $J(X)$
- [Abel–Jacobi map](../../jacobians-of-compact-riemann-surfaces/of-curve.md), for $\varphi_P$
- [Abelian scheme](../../../abelian-varieties/abelian-scheme.md), for abelian varieties over $\mathbb{C}$
- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md),
  for $X_\Gamma$ and $J$

## Proof depends on

- [Modular curve of a group of level $N$ and its standard model over $\mathbb{Q}$](../../../../NumberTheory/modular-forms-q-series/modular-forms/modular-curve-of-a-group-of-level-n.md),
  for the identification of $X_\Gamma(\mathbb{C})$ with $\mathfrak{H}^*/\Gamma$

## Expansion

This node is still to be broken down. A good expansion states and links:

- that the Jacobian variety $J_C$ of the curve $C$ is an abelian variety over $\mathbb{C}$;
- the analytic Jacobian $J^{an} = \Gamma(X, \Omega^1)^\vee / H_1(X, \mathbb{Z})$ and the map $g^P$ by integration, and the
  surjection $e \colon \Gamma(X, \Omega^1)^\vee \to J_C(\mathbb{C})$ obtained from the dual of $(f^P)^*$ on $1$-forms and the
  exponential map of $J_C(\mathbb{C})$ (Milne (1986c), p. 173);
- Abel's theorem and the Jacobi inversion theorem, which give that the kernel of $e$ is $H_1(X, \mathbb{Z})$, so that $e$
  induces an isomorphism $J^{an} \to J_C(\mathbb{C})$ carrying $g^P$ to $f^P$ (Milne's Theorem 2.5);
- the identification of $J(X)$ and $\varphi_P$ with $J^{an}$ and $g^P$.

## Sources

- J. S. Milne, "Jacobian varieties", in *Arithmetic Geometry* (G. Cornell and J. H. Silverman, eds.), Springer, 1986,
  167–212, <https://www.jmilne.org/math/articles/1986c.pdf>: p. 172 (the map $f^P$ on points, $Q \mapsto$ the class of
  $Q - P$); p. 173 (the analytic Jacobian $J^{an}$, the canonical map $g^P$, the surjection $e$, and Theorem 2.5: "The
  canonical surjection $e \colon \Gamma(C(\mathbb{C}), \Omega^1)^\vee \twoheadrightarrow J(\mathbb{C})$ induces an
  isomorphism $J^{an} \to J$ carrying $g^P$ into $f^P$", for $k = \mathbb{C}$, with its proof from Abel's theorem and the Jacobi inversion theorem).
- G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
  Japan 25 (1973), 523–544, <https://doi.org/10.2969/jmsj/02530523>: §1, p. 526 ("so that $J$ can naturally be defined
  over $\mathbf{Q}$", the jacobian variety of $\mathfrak{H}^*/\Gamma$ through the standard model).
