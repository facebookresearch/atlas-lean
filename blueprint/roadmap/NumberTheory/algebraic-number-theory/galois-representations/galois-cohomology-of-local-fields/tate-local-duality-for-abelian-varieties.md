# Tate local duality for abelian varieties

This node is still to be broken down. It covers Tate's duality between the Galois cohomology of an
abelian variety over a local field of characteristic $0$ and that of its dual, following Milne's
*Arithmetic Duality Theorems*, Chapter I, §3.

Let $k$ be a finite extension of $\mathbb{Q}_p$, with absolute Galois group $G_k$, let $A$ be an
[abelian variety](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over $k$ and let
$A^\vee$ be its [dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md).
Write $H^r(k, A) = H^r(G_k, A(\bar k))$, and identify $H^2(k, \mathbb{G}_m) = H^2(G_k, \bar k^\times)$ with
$\mathbb{Q}/\mathbb{Z}$ by the local invariant map.

1. **The pairing.** There is a canonical biadditive pairing

    $$H^r(k, A^\vee) \times H^{1-r}(k, A) \to H^2(k, \mathbb{G}_m) \cong \mathbb{Q}/\mathbb{Z}, \qquad r = 0, 1,$$

    the Yoneda pairing $\operatorname{Ext}^{r+1}_k(A, \mathbb{G}_m) \times H^{1-r}(k, A) \to H^2(k, \mathbb{G}_m)$
    transported along the isomorphisms $H^r(k, A^\vee) \cong \operatorname{Ext}^{r+1}_k(A, \mathbb{G}_m)$ that the
    Barsotti–Weil formula $A^\vee(\bar k) = \operatorname{Ext}^1_{\bar k}(A, \mathbb{G}_m)$ gives (Milne, Lemma I.3.1).
2. **Duality.** It induces an isomorphism of compact groups $A^\vee(k) \to H^1(k, A)^*$, where $A^\vee(k)$ has
    its $p$-adic topology, in which it is profinite, and $H^1(k, A)^* = \operatorname{Hom}(H^1(k, A), \mathbb{Q}/\mathbb{Z})$;
    and an isomorphism of discrete torsion groups $H^1(k, A^\vee) \to A(k)^*$, the group of continuous characters
    $A(k) \to \mathbb{Q}/\mathbb{Z}$. For $r \ge 2$, $H^r(k, A) = H^r(k, A^\vee) = 0$.
3. **Compatibility with finite level.** For every $n \ge 1$, let
    $e_n \colon A[n] \times A^\vee[n] \to \mu_n$ be the pairing given by the canonical identification of
    $A^\vee[n]$ with the Cartier dual of $A[n]$, and pair $H^1(k, A^\vee[n])$ with $H^1(k, A[n])$ through $e_n$ by
    [local Tate duality](local-tate-duality.md), in the form of the Yoneda pairing
    $\operatorname{Ext}^1_k(A[n], \mathbb{G}_m) \times H^1(k, A[n]) \to H^2(k, \mathbb{G}_m)$, which cup product identifies with
    the duality $H^1(k, A^\vee[n]) \times H^1(k, A[n]) \to H^2(k, \mu_n)$ (Milne, Theorem I.2.1 and Corollary I.2.3).
    Through the Kummer sequences $0 \to A[n] \to A \xrightarrow{n} A \to 0$ and
    $0 \to A^\vee[n] \to A^\vee \xrightarrow{n} A^\vee \to 0$ on $\bar k$-points, the pairing of 1 is compatible with these
    finite-level pairings: the connecting map $A^\vee(k)/nA^\vee(k) \to H^1(k, A^\vee[n])$ is adjoint to the map
    $H^1(k, A[n]) \to H^1(k, A)[n]$, and the map $H^1(k, A^\vee[n]) \to H^1(k, A^\vee)[n]$ is adjoint to the connecting
    map $A(k)/nA(k) \to H^1(k, A[n])$.
4. **The real numbers.** For an abelian variety $A$ over $\mathbb{R}$, with $G = \operatorname{Gal}(\mathbb{C}/\mathbb{R})$,
    the analogous pairing of Tate cohomology groups

    $$\hat H^r(G, A^\vee(\mathbb{C})) \times \hat H^{1-r}(G, A(\mathbb{C})) \to H^2(G, \mathbb{C}^\times) \cong \tfrac12\mathbb{Z}/\mathbb{Z}$$

    is a perfect pairing of finite groups for every $r \in \mathbb{Z}$. Here
    $\hat H^0(G, A(\mathbb{C})) = A(\mathbb{R})/A(\mathbb{R})^\circ = \pi_0(A(\mathbb{R}))$, the image of the norm map being
    the identity component $A(\mathbb{R})^\circ$.

## Expansion

A good expansion has pages for:

- the Barsotti–Weil formula $A^\vee(\bar k) = \operatorname{Ext}^1_{\bar k}(A, \mathbb{G}_m)$ and the vanishing of
  $\operatorname{Ext}^r_{\bar k}(A, \mathbb{G}_m)$ for $r \ge 2$ and of $\operatorname{Hom}_{\bar k}(A, \mathbb{G}_m)$, from which the
  spectral sequence gives $H^r(k, A^\vee) \cong \operatorname{Ext}^{r+1}_k(A, \mathbb{G}_m)$ (Milne, Lemma I.3.1, citing Serre,
  *Groupes algébriques et corps de classes*, 1959, VII §3, for the Barsotti–Weil formula and Oort, 1966, Proposition
  12.3, for the vanishing; neither read here);
- the open subgroup of $A(k)$ of finite index isomorphic to $\mathcal{O}_k^{\dim A}$, given by the logarithm of the
  formal group of $A$, with its consequences $A(k) = A(k)^\wedge$ and
  $\# A(k)/nA(k) = (\mathcal{O}_k : n\mathcal{O}_k)^{\dim A} \cdot \# A(k)[n]$ (Milne, Lemma I.3.3);
- the injectivity of $A^\vee(k) \to H^1(k, A)^*$ and the vanishing of $H^2(k, A)$ from the finite-level dualities
  and the snake lemma, and the surjectivity by comparing orders through the local Euler characteristic of $A[n]$
  (Milne, proof of Theorem I.3.2);
- the real case, from Tate duality for $\operatorname{Gal}(\mathbb{C}/\mathbb{R})$ applied to $A[2]$ and the two Kummer
  sequences for $n = 2$, and the computation of $\hat H^0$ (Milne, Remark I.3.7).

## Depends on

- [Abelian scheme](../../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties over a field
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for $A^\vee$ and, in its item 3, the identification of $A^\vee[n]$ with the Cartier dual of $A[n]$ that defines $e_n$
- [Isogenies of abelian schemes](../../../../AlgebraicGeometry/abelian-varieties/isogenies-of-abelian-schemes.md), for multiplication by $n$ as a finite étale surjection in characteristic $0$, which makes the Kummer sequences exact on $\bar k$-points
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the invariant maps $H^2(k, \mathbb{G}_m) \cong \mathbb{Q}/\mathbb{Z}$ and $H^2(\mathbb{R}, \mathbb{G}_m) \cong \tfrac12\mathbb{Z}/\mathbb{Z}$ (its item 2)
- [Local Tate duality](local-tate-duality.md), for the finite-level pairings of item 3
- [Cohomology of a profinite group with discrete coefficients](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cohomology-with-discrete-coefficients.md), for Galois cohomology
- [Cup products for profinite groups](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cup-products.md), for cup products
- [Tate cohomology groups of a finite group](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/tate-cohomology.md), for the Tate cohomology of $\operatorname{Gal}(\mathbb{C}/\mathbb{R})$
- [The long exact cohomology sequence](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/long-exact-cohomology-sequence.md) and [the long exact Tate cohomology sequence of a finite group](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/long-exact-tate-cohomology-sequence-of-a-finite-group.md), for the long exact sequences

## Proof depends on

- [Local Tate duality](local-tate-duality.md), for the finite-level dualities of $A[n]$ and $A^\vee[n]$
- [Local Euler characteristic formula](local-euler-characteristic-formula.md), for $\chi(k, A[n]) = (\mathcal{O}_k : n\mathcal{O}_k)^{-2\dim A}$ in the comparison of orders
- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for $\operatorname{cd}(G_k) = 2$, which gives $H^r(k, A) = 0$ for $r > 2$
- [Tate duality for the real numbers](tate-duality-for-the-real-numbers.md), for item 4
- [Dual abelian variety](../../../../AlgebraicGeometry/abelian-varieties/dual-abelian-variety.md), for $(n_A)^\vee = n_{A^\vee}$ and the Cartier duality of the kernels (its item 3), and biduality (its item 4), which lets the argument be applied with $A$ and $A^\vee$ interchanged

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §3: Lemma 3.1 (p. 40), Theorem 3.2 with its proof and Lemma 3.3 (pp. 41–43), Corollary 3.4 (p. 43,
  the statement of items 1 and 2), Remark 3.5 (p. 44, the description of the pairings by a Poincaré divisor and
  their compatibility with the $e_n$-pairings of finite level), Remark 3.7 (p. 46, the archimedean case), and the
  commutative diagram at the start of the proof of Theorem 3.2, for $r = 1$ (p. 42, item 3); §2, Theorem 2.1 and
  Corollary 2.3 (pp. 26–28, the finite-level duality as a Yoneda pairing and by cup product).
- J. Tate, "WC-groups over $\mathfrak{p}$-adic fields", Séminaire Bourbaki, exposé 156 (1957/58), the original
  source of the duality and of the description of the pairing in Milne's Remark I.3.5, as Milne's Notes to
  Chapter I, §3 (p. 48) say.
