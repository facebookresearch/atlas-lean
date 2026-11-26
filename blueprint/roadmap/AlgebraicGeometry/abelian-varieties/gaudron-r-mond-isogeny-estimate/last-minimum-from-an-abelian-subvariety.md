# Last minimum of a lattice of homomorphisms from an abelian subvariety

Let $K$ be a field of characteristic zero, $A$ and $B$ [abelian varieties](../abelian-scheme.md)
over $K$ with polarizations given by ample invertible sheaves $L$ on $A$ and $M$ on $B$, and $n \ge 1$
an integer. Let $p \colon A \times B^n \to A$ and $q_j \colon A \times B^n \to B$, $1 \le j \le n$, be
the projections. Let $H$ be an abelian subvariety of $A \times B^n$ defined over $K$ such that

1. $p(H) = A$, and
2. for every $f \in \operatorname{Hom}_K(A, B)$ there are integers $\ell \in \mathbb{N} \setminus
   \{0\}$ and $m_1, \dots, m_n \in \mathbb{Z}$ such that $H$ is contained in the kernel of $\ell f
   \circ p + \sum_{j=1}^n m_j q_j \colon A \times B^n \to B$.

Then

$$\Lambda(\operatorname{Hom}_K(A, B)) \le \Bigl( \frac{\deg H}{\deg A} \Bigr)^2,$$

where $\Lambda$ is the last minimum for the [Rosati metric](rosati-metric-on-homomorphisms.md) of
$L$ and $M$, $\deg A = \deg_L A$, and $\deg H$ is the degree of $H$ for the product polarization $L
\boxtimes M^{\boxtimes n}$ on $A \times B^n$.

## Expansion

The proof (*Polarisations et isogénies*, §7) replaces $H$ by an abelian subvariety $H' \subset H$
with $p(H') = A$, $\dim H' = \dim A$ and $\deg H' \le (\deg H)^2 / \deg A$ (Lemme 7.2: the
orthogonal in $H$ of the kernel of $p|_H$, with the degree bound for orthogonal abelian subvarieties
of *Théorème des périodes*, §2.2), and bounds the norms of the homomorphisms $q_j \circ \psi$, where
$\psi \colon A \to H'$ is the isogeny with $p \circ \psi = [s]$, $s = \deg(p|_{H'})$:
$\frac{s+1}{2s} \sum_{j=1}^n |q_j \circ \psi|^2 \le \deg H' / \deg A$ (Lemme 7.3). A good expansion has pages for: the expression of the Rosati norm by
intersection numbers, $|\varphi|^2 = \frac{2g}{(L^g)} (L^{g-1} \cdot \varphi^* M)$ (Proposition 2.8,
after Mumford, Theorem 1, p. 192); the projection formula and the binomial expansion of intersection
numbers on products used in Lemmes 7.2 and 7.3; and the orthogonal abelian subvariety and its degree.

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
