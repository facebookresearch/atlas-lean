# Selmer groups and the torsion of the Shafarevich–Tate group of an abelian variety

This node is still to be broken down. It covers the first results on the Selmer and Shafarevich–Tate groups of an
abelian variety over a number field, which the proof of the
[nondegeneracy of the Cassels–Tate pairing](nondegeneracy-of-the-cassels-tate-pairing.md) uses, following Milne's
*Arithmetic Duality Theorems*, Chapter I, §6.

Let $K$ be a number field, $\bar K$ an algebraic closure and $A$ an
[abelian variety](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md) over $K$. Write
$H^r(K, A) = H^r(G_K, A(\bar K))$ and, for a place $v$ of $K$, $H^r(K_v, A) = H^r(G_v, A(\bar K_v))$, reached by
restriction to a decomposition group $G_v$ and the inclusion $A(\bar K) \subseteq A(\bar K_v)$ (with Tate cohomology
for $r = 0$ at the archimedean places). The **Shafarevich–Tate group** is
$\text{Ш}(K, A) = \ker\bigl(H^1(K, A) \to \prod_v H^1(K_v, A)\bigr)$, and for an integer $m \ge 1$ the **$m$-Selmer
group** is $S^{(m)}(K, A) = \ker\bigl(H^1(K, A[m]) \to \prod_v H^1(K_v, A)\bigr)$, where $A[m] = A[m](\bar K)$.

1. **Local triviality almost everywhere.** For every class $a \in H^1(K, A)$, the image of $a$ in $H^1(K_v, A)$ is
   zero for all but finitely many places $v$.
2. **Selmer sequence.** The Kummer sequence $0 \to A[m] \to A(\bar K) \xrightarrow{m} A(\bar K) \to 0$ gives an exact
   sequence $0 \to A(K)/mA(K) \to S^{(m)}(K, A) \to \text{Ш}(K, A)[m] \to 0$.
3. **Finiteness.** $S^{(m)}(K, A)$ is finite. Hence $A(K)/mA(K)$ (the weak Mordell–Weil theorem) and
   $\text{Ш}(K, A)[m]$ are finite, and for every prime $\ell$ the $\ell$-primary part $\text{Ш}(K, A)(\ell)$ is the
   direct sum of a finite group and a divisible group isomorphic to $(\mathbb{Q}_\ell/\mathbb{Z}_\ell)^{r}$ for some
   $r \ge 0$; in particular $\text{Ш}(K, A)(\ell)$ modulo its maximal divisible subgroup is finite.
4. **Restricted ramification.** Let $S$ be a finite set of places of $K$ containing the archimedean places, the
   places where $A$ has bad reduction and those above the primes dividing $m$, let $K_S$ be the maximal extension of
   $K$ in $\bar K$ unramified outside $S$ and $G_S = \operatorname{Gal}(K_S/K)$. Then $A[m] \subseteq A(K_S)$,
   multiplication by $m$ is surjective on $A(K_S)$, and inflation identifies the $m$-primary part
   $\text{Ш}(K, A)(m)$ with that of
   $\text{Ш}_S(K, A) = \ker\bigl(H^1(G_S, A(K_S)) \to \bigoplus_{v \in S} H^1(K_v, A)\bigr)$, and $S^{(m)}(K, A)$ with
   $\ker\bigl(H^1(G_S, A[m]) \to \bigoplus_{v \in S} H^1(K_v, A)\bigr)$.

## Expansion

A good expansion has pages for:

- the reduction lemma: if $A$ has good reduction outside $S$ and $m$ is a unit outside $S$, then $A[m]$ is unramified
  outside $S$ and $m \colon A(K_S) \to A(K_S)$ is onto, because $A$ extends to an abelian scheme over the ring of
  $S$-integers, on which multiplication by $m$ is finite étale (Milne, Lemma I.6.1);
- the vanishing of $H^1(G_v/I_v, A(K_v^{\mathrm{un}}))$ at a place $v$ of good reduction, by Lang's theorem on torsors
  under connected groups over finite fields and Hensel's lemma (Milne, Proposition I.3.8 and Remark I.3.9);
- items 1, 2 and 4 from these and the inflation–restriction sequence (Milne, Lemma I.6.3, Propositions I.6.4 and
  I.6.5, Corollary I.6.6), and item 3 from the finiteness of $H^1(G_S, A[m])$ (Milne, Proposition I.6.2 and Remark
  I.6.7).

## Depends on

- [Abelian scheme](../../../AlgebraicGeometry/abelian-varieties/abelian-scheme.md), for abelian varieties and, through abelian schemes over the local rings, good reduction
- [Tate–Shafarevich groups of Galois modules](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/tate-shafarevich-groups.md), of which $\text{Ш}(K, A)$ and $\text{Ш}_S(K, A)$ are instances for the discrete modules $A(\bar K)$ and $A(K_S)$
- [Galois groups with restricted ramification and their modules](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/galois-groups-with-restricted-ramification.md), for $K_S$, $G_S$ and the local groups in item 4
- [Isogenies of abelian schemes](../../../AlgebraicGeometry/abelian-varieties/isogenies-of-abelian-schemes.md), for multiplication by $m$ and the finite group scheme $A[m]$ in the Kummer sequence

## Proof depends on

- [Finiteness and cohomological dimension of Galois groups with restricted ramification](../../algebraic-number-theory/galois-representations/galois-cohomology-of-number-fields/finiteness-and-cohomological-dimension-of-g-s.md), for the finiteness of $H^1(G_S, A[m])$ when $S$ is finite (its item 2)
- [Néron model of an abelian variety](../../../AlgebraicGeometry/abelian-varieties/neron-model.md), for the abelian scheme over the ring of $S$-integers extending $A$ and for the reduction of $A$ at the places outside $S$
- [Isogenies of abelian schemes](../../../AlgebraicGeometry/abelian-varieties/isogenies-of-abelian-schemes.md), for multiplication by $m$ as a finite étale surjection over the ring of $S$-integers (its item 2)
- [Cohomology of profinite groups](../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for inflation, restriction and the inflation–restriction sequence, and for the cohomology of $\hat{\mathbb{Z}}$

## Sources

- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §6: Lemma 6.1 (p. 73), Proposition 6.2 (p. 74, the weak Mordell–Weil theorem), Lemma 6.3 (p. 74, item
  1), the definitions of $\text{Ш}_S(K, A)$ and the Selmer groups (pp. 74–75), Proposition 6.4 (p. 75, item 2),
  Proposition 6.5 and Corollary 6.6 (pp. 75–77, item 4), Remark 6.7 (p. 77, item 3); §3, Proposition 3.8 and Remark
  3.9 (pp. 46–47).
- J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics 106, Springer, 2009:
  Chapter X, Theorem 4.2 (items 2 and 3 for an isogeny of elliptic curves).
