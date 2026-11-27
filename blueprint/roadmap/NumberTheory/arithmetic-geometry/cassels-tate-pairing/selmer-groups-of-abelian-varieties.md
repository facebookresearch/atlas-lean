# Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety

This node covers the first results on the Selmer and Shafarevich–Tate groups of an
abelian variety over a number field, which the proof of the
[nondegeneracy of the Cassels–Tate pairing](nondegeneracy-of-the-cassels-tate-pairing.md) uses, following Milne's
*Arithmetic Duality Theorems*, Chapter I, §6.

Let $K$ be a number field, $\bar K$ an algebraic closure and $A$ an
[abelian variety](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over $K$. Write
$H^r(K, A) = H^r(G_K, A(\bar K))$ and, for a place $v$ of $K$, $H^r(K_v, A) = H^r(G_v, A(\bar K_v))$ (with Tate
cohomology for $r = 0$ at the archimedean places). Localization at $v$ is restriction to a decomposition group $G_v$
followed by the extension of coefficients along $A(\bar K) \subseteq A(\bar K_v)$; on $H^r(K, A[m])$ it is
restriction followed by $A[m] \subseteq A(\bar K_v)$. The **Shafarevich–Tate group** is
$\text{Ш}(K, A) = \ker\bigl(H^1(K, A) \to \prod_v H^1(K_v, A)\bigr)$, and for an integer $m \ge 1$ the **$m$-Selmer
group** is $S^{(m)}(K, A) = \ker\bigl(H^1(K, A[m]) \to \prod_v H^1(K_v, A)\bigr)$, where $A[m] = A[m](\bar K)$.

1. **Local triviality almost everywhere.** For every class $a \in H^1(K, A)$, the image of $a$ in $H^1(K_v, A)$ is
   zero for all but finitely many places $v$.
2. **Selmer sequence.** The Kummer sequence $0 \to A[m] \to A(\bar K) \xrightarrow{m} A(\bar K) \to 0$ gives an exact
   sequence $0 \to A(K)/mA(K) \to S^{(m)}(K, A) \to \text{Ш}(K, A)[m] \to 0$.
3. **Finiteness.** $S^{(m)}(K, A)$ is finite. Hence $A(K)/mA(K)$ (the weak Mordell–Weil theorem) and
   $\text{Ш}(K, A)[m]$ are finite, and for every prime $\ell$ the $\ell$-primary part $\text{Ш}(K, A)(\ell)$ is an
   extension of a finite group by a divisible group isomorphic to $(\mathbb{Q}_\ell/\mathbb{Z}_\ell)^{r}$ for some
   $r \ge 0$, finite because $\text{Ш}(K, A)[\ell]$ is; in particular $\text{Ш}(K, A)(\ell)$ modulo its maximal divisible subgroup is finite.
4. **Restricted ramification.** Let $S$ be a finite set of places of $K$ containing the archimedean places, the
   places where $A$ has bad reduction and those above the primes dividing $m$, let $K_S$ be the maximal extension of
   $K$ in $\bar K$ unramified outside $S$ and $G_S = \operatorname{Gal}(K_S/K)$. Then $A[m] \subseteq A(K_S)$,
   multiplication by $m$ is surjective on $A(K_S)$, and inflation identifies the $m$-primary part
   $\text{Ш}(K, A)(m)$ with that of
   $\text{Ш}_S(K, A) = \ker\bigl(H^1(G_S, A(K_S)) \to \bigoplus_{v \in S} H^1(K_v, A)\bigr)$, and $S^{(m)}(K, A)$ with
   $\ker\bigl(H^1(G_S, A[m]) \to \bigoplus_{v \in S} H^1(K_v, A)\bigr)$. Here the localization of the restricted group
   is again a restriction, along $G_v \to G_K \to G_S$, followed by the extension of coefficients along
   $A(K_S) \subseteq A(\bar K_v)$.
5. **Places of good reduction.** If $A$ has good reduction at a finite place $v$ not above a prime dividing $m$, then
   $A[m] \subseteq A(K_v^{\mathrm{un}})$, multiplication by $m$ is onto $A(K_v^{\mathrm{un}})$, and
   $H^1(G_v/I_v, A(K_v^{\mathrm{un}})) = 0$, where $K_v^{\mathrm{un}}$ is the maximal unramified extension of $K_v$ and
   $I_v$ the inertia group.

These groups are defined with the coefficients $A(\bar K_v)$ at the places. They are therefore not literally the
groups $\text{Ш}^1(G_S, M)$ of [Tate–Shafarevich groups of Galois modules](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/tate-shafarevich-groups.md),
which keep the same module $M$ at the places, but their analogues with the coefficients extended locally. What
compares the two kinds of local groups at a finite place is Milne's Remark I.3.10 (a) (ii): for an abelian variety $A$
over the fraction field $K'$ of an excellent henselian discrete valuation ring with finite residue field, the map
$H^1(K', A) \to H^1(\hat K', A)$ to the completion is an isomorphism.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the reduction lemma: if $A$ has good reduction outside $S$ and $m$ is a unit outside $S$, then $A[m]$ is unramified
  outside $S$ and $m \colon A(K_S) \to A(K_S)$ is onto, because $A$ extends to an abelian scheme over the ring of
  $S$-integers, on which multiplication by $m$ is finite étale (Milne, Lemma I.6.1);
- the vanishing of $H^1(G_v/I_v, A(K_v^{\mathrm{un}}))$ at a place $v$ of good reduction, by Lang's theorem on torsors
  under connected groups over finite fields and Hensel's lemma (Milne, Proposition I.3.8 and Remark I.3.9);
- items 1, 2 and 4 from these and the inflation–restriction sequence (Milne, Lemma I.6.3, Propositions I.6.4 and
  I.6.5, Corollary I.6.6, the equality of the Selmer groups following from Corollary I.6.6 and Proposition I.6.4 by
  the five lemma), item 3 from the finiteness of $H^1(G_S, A[m])$ (Milne, Proposition I.6.2 and Remark I.6.7), and
  item 5 from the proof of Lemma I.6.1 over the henselian local ring at $v$ and Proposition I.3.8.

## Depends on

- [Abelian scheme](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties and, through abelian schemes over the local rings, good reduction
- [Tate–Shafarevich groups of Galois modules](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/tate-shafarevich-groups.md), the fixed-coefficient analogue of $\text{Ш}(K, A)$ and $\text{Ш}_S(K, A)$, which here extend the coefficients from $A(\bar K)$ or $A(K_S)$ to $A(\bar K_v)$ at each place
- [Galois groups with restricted ramification and their modules](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/galois-groups-with-restricted-ramification.md), for $K_S$, $G_S$ and the local groups in item 4
- [Isogenies of abelian schemes](../../../AlgebraicGeometry/abelian-varieties/isogenies-of-abelian-schemes.md), for multiplication by $m$ and the finite group scheme $A[m]$ in the Kummer sequence

## Proof depends on

- [Finiteness and cohomological dimension of Galois groups with restricted ramification](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/finiteness-and-cohomological-dimension-of-g-s.md), for the finiteness of $H^1(G_S, A[m])$ when $S$ is finite (its item 2)
- [Néron model of an abelian variety](../../../AlgebraicGeometry/abelian-varieties/neron-model.md), for the abelian scheme over the ring of $S$-integers extending $A$ and for the reduction of $A$ at the places outside $S$
- [Isogenies of abelian schemes](../../../AlgebraicGeometry/abelian-varieties/isogenies-of-abelian-schemes.md), for multiplication by $m$ as a finite étale surjection over the ring of $S$-integers (its item 2)
- [Cohomology of profinite groups](../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for inflation, restriction and the inflation–restriction sequence, and for the cohomology of $\hat{\mathbb{Z}}$

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §6: Lemma 6.1 (p. 73, items 4 and 5), Proposition 6.2 (p. 74, the weak Mordell–Weil theorem), Lemma 6.3 (p. 74, item
  1), the definitions of $\text{Ш}_S(K, A)$ and the Selmer groups (pp. 74–75), Proposition 6.4 (p. 75, item 2),
  Proposition 6.5 and Corollary 6.6 (pp. 75–77, item 4), Remark 6.7 (p. 77, item 3); §3, Proposition 3.8 and Remark
  3.9 (pp. 46–47, item 5), Remark 3.10 (a) (pp. 47–48, the comparison with the completion).
