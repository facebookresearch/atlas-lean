# Isogeny estimate with auxiliary heights

In the setting of the [bounds for the last minima](last-minimum-bounds.md): $k$ is a number field,
$A$ and $A'$ are [abelian varieties](../abelian-scheme.md) over $k$, with $g = \dim A$, isogenous over
an extension $K$ of $k$ with $k \subset K \subset k_1$, where $k_1$ is the smallest extension of $k$
over which all endomorphisms of $A \times A'$ are defined, and $A''$, $A'''$, $M$ and $P$ are as
there. Then there is a pair of [isogenies](../isogenies-of-abelian-schemes.md) $\varphi_1 \colon A
\to A'$ and $\varphi_2 \colon A' \to A$ defined over $K$ with

$$\max(\deg \varphi_1, \deg \varphi_2) \le (9g)^{96 g^4} P^{2^{10} g^3}.$$

This is the case of the isogeny estimate in Gaudron and Rémond's Lemme 9.3, which states their four
main theorems with $(9g)^{96 g^4} P^{2^{10} g^3}$ in place of $\kappa(A)$. The bound still involves
the heights of $A'$, $A''$ and $A'''$ through $M$; the last step of the
[Gaudron–Rémond isogeny estimate](exists-isogenies-degree-le-kappa.md) removes them.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the endomorphism algebra of a simple abelian variety, a division algebra, and of a power of one
  (Milne, *Abelian Varieties*, Chapter I, §10, p. 43), for $d_i \le d_i \nu(A_i) \le 2 g_i^2$;
- the bounds on $\nu$, $\nu(A) \le 2 g^2$ among them (*Polarisations et isogénies*, p. 2091);
- the computation of Lemme 9.3 (pp. 2099–2100) described below.

The proof inserts the bounds for $\Lambda \Lambda'$ and $\Lambda_i$ of the [bounds for the last
minima](last-minimum-bounds.md) into item 2 of [isogeny degrees from last
minima](isogeny-degree-from-last-minima.md), which is at most $(10g)^{5g} (\Lambda \Lambda')^{4g}
\prod_i \Lambda_i^{8 n_i^2 g_i d_i}$, and gets the bound $g^{5g} (9g)^{32 g^2 + 32 g \sum_i n_i^2 g_i
d_i} P^{256 (g \nu(A) + \sum_i n_i^2 g_i d_i \nu(A_i))}$. It then uses $d_i \le d_i \nu(A_i) \le 2
g_i^2$, from the injection of $\operatorname{End}_K(A_i) \otimes \mathbb{Q}$, a division algebra since
$A_i$ is simple over $K$, into each $\operatorname{End}_{k_1}(C_{i,j}^{m_{i,j}}) \otimes
\mathbb{Q}$, together with $\nu(A) \le 2 g^2$ and $g^{5g} \le (9g)^{32 g^2 (g^2 - 1)}$.

## Depends on

- [Bounds for the last minima of the lattices of homomorphisms](last-minimum-bounds.md), for the
  setting and the constant $P$
- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for isogenies and their degree
- [Abelian scheme](../abelian-scheme.md), for abelian varieties over $k$

## Proof depends on

- [Isogeny degrees from last minima](isogeny-degree-from-last-minima.md), item 2
- [Bounds for the last minima of the lattices of homomorphisms](last-minimum-bounds.md), item 2
- [Abelian subvariety of bounded degree from the period theorem](abelian-subvariety-from-the-period-theorem.md),
  for the invariant $\nu$ and its bound $\nu(A) \le 2g^2$

## Sources

- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: Lemme 9.3 and its proof, pp. 2099–2100; the invariant
  $\nu$ and its properties, p. 2091; the final bound of §6, p. 2089.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §10, p. 43 (the endomorphism algebra
  of a simple abelian variety is a division algebra, and $\operatorname{End}^0(A^n) \simeq M_n(D)$).
