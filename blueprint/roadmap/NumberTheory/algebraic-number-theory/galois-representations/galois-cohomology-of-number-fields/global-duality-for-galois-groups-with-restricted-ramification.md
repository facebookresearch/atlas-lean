# Global duality for Galois groups with restricted ramification

This node is still to be broken down. It covers the results on the cohomology of the Galois group
$G_S = \operatorname{Gal}(F_S/F)$ of the maximal extension $F_S$ of a number field $F$ unramified outside a set
$S \supseteq S_\infty$ of places that come before Poitou–Tate duality: the cohomology of the $S$-units and
$S$-idèle classes, the global duality theorem coming from the class formation of the $S$-idèle classes, the
local cohomology of global modules, and the lemmas of Neukirch–Schmidt–Wingberg VIII §6 that precede
(8.6.7). None of them uses the finiteness theorems, Poitou–Tate duality or the Poitou–Tate sequence; the later
steps of the proof of the Poitou–Tate sequence, which do, form the node on the
[exactness of the Poitou–Tate complex](exactness-of-the-poitou-tate-complex.md). It follows
Neukirch–Schmidt–Wingberg, Chapter VIII, §§3–7, and Milne's *Arithmetic Duality Theorems*, Chapter I, §4.

A good expansion has pages for:

1. the roots of unity of order in $\mathbb{N}(S)$ in $F_S$ and the $\mathbb{N}(S)$-divisibility of the
   $S$-units $\mathcal{O}_S^\times$ of $F_S$ (NSW (8.3.4));
2. the cohomology of the $S$-idèles $I_S$, of the $S$-idèle classes $C_S$ and of $\mathcal{O}_S^\times$ (NSW
   (8.3.5)–(8.3.13); Milne, Lemma I.4.1, Propositions I.4.2–4.3, Lemmas I.4.4–4.5), in separate steps:
   - the exact sequence $0 \to C_{K,S} \to C_S(K) \to \mathrm{Cl}_S(K) \to 0$ for finite $K/F$ inside $F_S$ (8.3.5);
   - the **principalisation** $\varinjlim_K \mathrm{Cl}_S(K) = 0$: every ideal of $\mathcal{O}_{K,S}$ becomes principal in
     the maximal subfield of the Hilbert class field of $K$ completely split at the places of $S$, by the
     **principal ideal theorem**, which needs its own page; with (8.3.5) it gives $C_S = \varinjlim_K C_S(K)$ and
     $C_S^{\operatorname{Gal}(F_S/K)} = C_S(K)$ (8.3.6). This step does not come from the finite generation of the
     $S$-units;
   - the comparison $\hat H^i(\operatorname{Gal}(K/F), C_S(K)) \cong \hat H^i(\operatorname{Gal}(K/F), C_K)$ (8.3.7), the
     cohomology of $I_S$ (8.3.8), the class formation $(G_S, C_S)$ for the primes in $\mathbb{N}(S)$ with its
     reciprocity isomorphism (8.3.9), (8.3.10) (Milne, Proposition I.4.2), the cohomology of $\mathcal{O}_S^\times$
     (8.3.11), (8.3.12), and the divisibility of the connected component $D_S$ of $C_S(F)$ (8.3.13);
3. the global duality theorem (NSW §4; Milne, Theorem I.4.6 and Corollary I.4.7), whose degrees depend on the
   coefficients:
   - for a Galois extension $K/F$ unramified outside $S$ with group $G$ and a finitely generated $\mathbb{Z}$-free
     $G$-module $A$, cup product gives $\hat H^i(G, \operatorname{Hom}(A, C_S(K))) \cong \hat H^{2-i}(G, A)^\vee$ for all
     $i \in \mathbb{Z}$ (8.4.1);
   - the norm-one $S$-idèle classes $C_S^0$ form a level-compact formation module whose universal norm group
     $N_{F_S/K} C_S^0$ is divisible for every finite subextension $K$ (8.4.2)(i), and
     $\hat H^i(G_S, \operatorname{Hom}(A, C_S^0)) \cong \hat H^i(G_S, \operatorname{Hom}(A, C_S))$ for every finitely generated $A$
     (8.4.2)(ii);
   - the abstract duality theorem for a level-compact formation module whose universal norm groups are divisible
     (NSW (3.1.11)(i)), applied to $(G_S, C_S^0)$ with both properties of (8.4.2)(i): for a discrete $G_S$-module $A$
     finitely generated as an abelian group, cup product gives topological isomorphisms
     $\hat H^i(G_S, \operatorname{Hom}(A, C_S^0)) \cong \hat H^{2-i}(G_S, A)^\vee$ for all $i \le 0$, and for all
     $i \in \mathbb{Z}$ if $A$ is $\mathbb{Z}$-free (8.4.4); with the topologies of (8.4.5);
4. the local cohomology of global modules: the topologies on the local and global groups, the isomorphisms
   $\Xi^i \colon P^i(G_S, A) \cong P^{2-i}(G_S, A')^\vee$ for finite $A$ (NSW (8.5.2), which rests on the
   unramified subgroups being exact annihilators), and the Shapiro maps $\mathrm{sh}^i$ (NSW (8.5.1)–(8.5.5));
5. the lemmas (8.6.3)–(8.6.6): the description $\text{Ш}^1(G_S, \mathbb{Z}/m\mathbb{Z}) \cong \operatorname{Hom}(\mathrm{Cl}_S(F), \mathbb{Z}/m\mathbb{Z})$
   and $\text{Ш}^1(G_S, \mathbb{Z}') \cong \mathrm{Cl}_S(F)$ by class field theory and Hilbert's Theorem 90 (8.6.3);
   the boundary map $C_S(A)^{G_S} \to H^1(G_S, A')$ and the finiteness of $\text{Ш}^1(G_S, A')$ (8.6.4), whose proof
   uses class field theory together with the principal ideal theorem again; the kernel of
   $\xi^i = \Xi^i \circ \lambda^i$ (8.6.5); and the compatibility diagrams (8.6.6); Milne, Lemmas I.4.8–4.9;
6. the Galois module structure of the $S$-units used by the global Euler characteristic formula (NSW (8.7.1)–(8.7.3)).

## Depends on

- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md), for $F_S$, $G_S$, $\mathbb{N}(S)$, the $S$-units $\mathcal{O}_S^\times$, the duals, the local groups, $P^i$ and $\lambda^i$
- [Tate–Shafarevich groups of Galois modules](tate-shafarevich-groups.md), for the groups $\text{Ш}^1(G_S, -)$ of item 5
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for Tate cohomology, class formations and level-compact formation modules in items 2 and 3
- [Topological idele class group](../../adeles-class-field-theory/adeles-and-ideles/topological-idele-class-group.md), for the idèle class groups $C_K$, of which the $S$-idèle class groups $C_S(K)$ are quotients (items 2 and 3)
- [Adelic norm](../../adeles-class-field-theory/adeles-and-ideles/adelic-norm.md), for the norm of idèle classes, whose kernel defines $C_S^0$ (item 3)
- [Hilbert class field of a number field](../../adeles-class-field-theory/hilbert-class-field/is-hilbert-class-field.md), for the Hilbert class field of $K$, whose maximal subfield completely split at the places of $S$ is the field of the principalisation in item 2; that the ideals become principal there is the principal ideal theorem, listed under Expansion
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md), for the local pairings defining $\Xi^i$ in item 4
- [Tate duality for the real numbers](../galois-cohomology-of-local-fields/tate-duality-for-the-real-numbers.md), for those pairings at the archimedean places

## Proof depends on

- [Fundamental class of a finite Galois extension of number fields](../../adeles-class-field-theory/reciprocity-law/fundamental-class.md), for the class formation of the idèle classes and their invariant maps, from which item 2 builds that of the $S$-idèle classes
- [S-unit theorem](../../discriminants-ramification/s-unit-theorem.md), for the finite generation and the rank of the groups of $S$-units of the finite subextensions of $F_S$, used for their Galois module structure in item 6 (NSW (8.7.2)); the principalisation of item 2 is a separate input
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md), for the local duality in items 4 and 5
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the exact annihilators behind (8.5.2) in item 4
- [Tate duality for the real numbers](../galois-cohomology-of-local-fields/tate-duality-for-the-real-numbers.md), for the archimedean places in items 3 and 4
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the Tate–Nakayama theorem and the duality theorem (3.1.11)(i) for a level-compact formation module with divisible universal norm groups, which give the duality of item 3 in the degrees $i \le 0$ for every finitely generated $A$, and in all degrees if $A$ is $\mathbb{Z}$-free
- [Hilbert's Theorem 90 for the multiplicative group](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), for the vanishing of the local groups $H^1(F_v, \bar F_v^\times)$, from the finite theorem by the continuous direct limit over the finite Galois extensions of $F_v$ (items 1 and 6 of the cohomology of profinite groups), so that $\text{Ш}^1(G_S, \mathbb{Z}')$ is all of $H^1(G_S, \mathcal{O}_S^\times)$ in (8.6.3) (item 5); that global group is $\mathrm{Cl}_S(F)$ by (8.3.11)(ii), not zero
- [Existence theorem of global class field theory](../../adeles-class-field-theory/existence-theorem/existence-of-class-fields.md), for the class field of the open subgroup of $C_F$ represented by the idèles with arbitrary components at the places of $S$ and unit components elsewhere, the maximal abelian extension of $F$ inside $F_S$ in which the places of $S$ split completely, whose Galois group is $\mathrm{Cl}_S(F)$ in (8.6.3), and of the corresponding subgroups after base change to the finite extensions $K$ in (8.6.4) (item 5)
- [Global reciprocity law](../../adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), for the Artin isomorphisms of those class fields, $\mathrm{Gal} \cong C_F/N \cong \mathrm{Cl}_S(F)$, in (8.6.3) and (8.6.4) (item 5)

## Expansion

A good expansion also states and links:

- the principal ideal theorem (Neukirch–Schmidt–Wingberg, proofs of (8.3.6), p. 456, and of (8.6.4)), for the principalisation $\varinjlim_K \mathrm{Cl}_S(K) = 0$ of item 2 and the finiteness of $\text{Ш}^1(G_S, A')$ in (8.6.4) (item 5)

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VIII, §3 (8.3.4)–(8.3.13)
  (the principal ideal theorem in the proof of (8.3.6), p. 456), §4 (8.4.1)–(8.4.5) ((8.4.2)(i): "a level-compact formation module with
  divisible universal norm group"; (8.4.4), obtained by "applying the duality theorem (3.1.11)(i)": "for all
  $i \le 0$. This assertion holds for all $i \in \mathbb{Z}$ if $A$ is assumed to be $\mathbb{Z}$-free"), Chapter III, §1,
  (3.1.11) Duality Theorem (i), §5 (8.5.1)–(8.5.5), §6 (8.6.3)–(8.6.6) (the principal ideal theorem in the proof of (8.6.4),
  p. 482), §7 (8.7.1)–(8.7.3).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §4, Lemma 4.1 to Lemma 4.9.
