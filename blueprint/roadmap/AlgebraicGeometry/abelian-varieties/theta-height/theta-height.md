# Theta height

Let $r \ge 2$ be an even integer, $A$ an [abelian variety](../abelian-scheme.md) of dimension $g$
over $\overline{\mathbb{Q}}$, and $L$ an ample line bundle on $A$ that is
[symmetric](../../not-yet-classified/canonical-polarization-data/is-symmetric.md),
$[-1]^* L \cong L$, and defines a principal [polarization](../polarization.md): $\varphi_L \colon A
\to A^\vee$ is an isomorphism. Choose a
[theta embedding of level $r$](theta-structure.md) $\Theta \colon A \to
\mathbb{P}_{\overline{\mathbb{Q}}}^{r^{2g} - 1}$ attached to $L$, constructed over the algebraically
closed field $\overline{\mathbb{Q}}$, so that $\Theta(0) \in \mathbb{P}^{r^{2g} - 1}(\overline{\mathbb{Q}})$.
The **theta height** of $A$ with respect to $L$ is

$$h_\Theta(A, L) = h_2(\Theta(0)),$$

the [$\ell^2$-height](../../../NumberTheory/heights-mahler-measure/l2-height-of-projective-points.md)
of the image of the origin. The point $\Theta(0)$ is determined by $(A, L)$ up to the action of
the finite group $G$ of the theta embedding, which permutes the coordinates and multiplies them by
roots of unity and so changes no $\|\cdot\|_{\mathfrak{p}}$ and no $\ell^2$ norm; the
$\ell^2$-height is computed in any number field containing a set of homogeneous coordinates of
$\Theta(0)$, which may be larger than a field over which $A$, $L$ and the points of order dividing
$r^2$ are defined (see the theta embedding page). So $h_\Theta(A, L) \ge 0$ depends only on $(A, L)$ up to
isomorphism over $\overline{\mathbb{Q}}$ and on $r$, which the notation leaves implicit.

Pazuki also describes $\Theta(0)$ analytically (§2.3.4, pp. 30–31): for an embedding
$\overline{\mathbb{Q}} \to \mathbb{C}$ and $\tau$ in the Siegel upper half space with
$A(\mathbb{C}) \cong \mathbb{C}^g / (\mathbb{Z}^g + \tau \mathbb{Z}^g)$ as principally polarized
complex abelian varieties, for a suitable choice of theta coordinates (up to the action of $G$)
$\Theta(0)$ has projective coordinates the theta constants
$\theta_{(m_1, m_2)}(\tau, 0)$, $m_1, m_2 \in \{0, \frac{1}{r}, \dots, \frac{r - 1}{r}\}^g$, so
that $h_\Theta(A, L)$, which no such choice changes, is the $\ell^2$-height of this point of
$\mathbb{P}^{r^{2g} - 1}(\overline{\mathbb{Q}})$. Pazuki notes that some authors, Mumford among
them, use instead the coordinates $\theta_{(m, 0)}(r^2 \tau, 0)$, $m \in \frac{1}{r^2}
\mathbb{Z}^g / \mathbb{Z}^g$; the definition here uses the former.

## Depends on

- [Theta structures of level r and theta embeddings](theta-structure.md), for $\Theta$ and its
  ambiguity group $G$
- [ℓ²-height of a point of projective space](../../../NumberTheory/heights-mahler-measure/l2-height-of-projective-points.md),
  for $h_2$
- [Is Symmetric](../../not-yet-classified/canonical-polarization-data/is-symmetric.md), for
  symmetric line bundles
- [Polarization](../polarization.md), for principal polarizations
- [Abelian scheme](../abelian-scheme.md), for abelian varieties over a field

## Proof depends on

- [Theta structures of level r and theta embeddings](theta-structure.md), for the independence of
  $\Theta(0)$, up to $G$, from the choices made

## Sources

- F. Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012), 19–49,
  <https://doi.org/10.24033/bsmf.2623>, Definition 2.6 and the discussion after it, §2.3.4,
  pp. 30–31; arXiv:0907.1458.
