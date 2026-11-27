# Last minimum of a lattice of homomorphisms from an abelian subvariety

Let $K$ be a field of characteristic zero, $A$ and $B$ [abelian varieties](../abelian-scheme.md)
over $K$ with [polarizations](../polarization.md) $\lambda_A$ and $\lambda_B$ defined over $K$, and
$n \ge 1$ an integer. Let $p \colon A \times B^n \to A$ and $q_j \colon A \times B^n \to B$, $1 \le j
\le n$, be the projections. Let $H$ be an abelian subvariety of $A \times B^n$ defined over $K$ such
that

1. $p(H) = A$, and
2. for every $f \in \operatorname{Hom}_K(A, B)$ there are integers $\ell \in \mathbb{N} \setminus
   \{0\}$ and $m_1, \dots, m_n \in \mathbb{Z}$ such that $H$ is contained in the kernel of $\ell f
   \circ p + \sum_{j=1}^n m_j q_j \colon A \times B^n \to B$.

Then

$$\Lambda(\operatorname{Hom}_K(A, B)) \le \Bigl( \frac{\deg H}{\deg A} \Bigr)^2,$$

where $\Lambda$ is the last minimum for the [Rosati metric](rosati-metric-on-homomorphisms.md) of
$\lambda_A$ and $\lambda_B$, and the degrees are taken for $\lambda_A$ and for the product
polarization of $A \times B^n$: over an algebraic closure $\bar K$, with ample invertible sheaves
$L$ on $A_{\bar K}$ and $M$ on $B_{\bar K}$ such that $\lambda_A = \phi_L$ and $\lambda_B = \phi_M$,
$\deg A = (L^{\dim A})$ and $\deg H$ is the degree of $H_{\bar K}$ for $L \boxtimes M^{\boxtimes n}$.

## Expansion

This node is still to be broken down. A good expansion states and links:

- Lemme 7.2 (*Polarisations et isogénies*, pp. 2089–2090): for polarized abelian varieties $A$ and
  $C$ and an abelian subvariety $H$ of $A \times C$ with $p(H) = A$, there is an abelian subvariety
  $H' \subset H$ with $p(H') = A$, $\dim H' = \dim A$ and $\deg H' \le (\deg H)^2 / \deg A$; $H'$ is
  the orthogonal in $H$ of the kernel of $p|_H$, and the bound uses the degree of orthogonal abelian
  subvarieties (*Théorème des périodes*, §2.2);
- Lemme 7.3 (p. 2090): for such an $H' \subset A \times B^n$, with $s = \deg(p|_{H'})$ and
  $\psi \colon A \to H'$ the isogeny with $p|_{H'} \circ \psi = [s]$,

    $$s + \frac{1}{2s} \sum_{j=1}^n |q_j \circ \psi|^2 \le \frac{\deg H'}{\deg A};$$

- the expression of the Rosati norm by intersection numbers, $|\varphi|^2 = \frac{2g}{(L^{g})}
  (L^{g-1} \cdot \varphi^* M)$ for $\varphi \in \operatorname{Hom}_K(A, B)$, $g = \dim A$
  (Proposition 2.8, p. 2066, after Mumford, Theorem 1, p. 192), with the projection formula and the
  binomial expansion of intersection numbers on products used in Lemmes 7.2 and 7.3;
- the conclusion (p. 2091): with $x = \max_j |q_j \circ \psi|$, $x \le s + x^2/(2s) \le (\deg H /
  \deg A)^2$, and the $q_j \circ \psi$ span $\operatorname{Hom}_K(A, B) \otimes \mathbb{Q}$ by
  hypothesis 2.

## Depends on

- [Rosati metric on lattices of homomorphisms](rosati-metric-on-homomorphisms.md), for
  $\operatorname{Hom}_K(A, B)$ and $\Lambda$
- [Abelian scheme](../abelian-scheme.md), for abelian varieties over $K$
- [Polarization](../polarization.md)

## Proof depends on

- [Rosati metric on lattices of homomorphisms](rosati-metric-on-homomorphisms.md), for the last
  minimum, which is bounded by exhibiting elements $q_j \circ \psi$ that span
  $\operatorname{Hom}_K(A, B) \otimes \mathbb{Q}$

## Sources

- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: Proposition 7.1, p. 2089, with Lemmes 7.2 and 7.3 and
  the proof, pp. 2089–2091; Proposition 2.8, p. 2066.
- É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math.
  Helv. 89 (2014), 343–403, <https://doi.org/10.4171/CMH/322>: §2.2, p. 351 (degree of the orthogonal
  abelian subvariety), cited in the proof of Lemme 7.2.
