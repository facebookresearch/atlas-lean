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
2. the cohomology of the $S$-idèles $I_S$, of the $S$-idèle classes $C_S$ and of $\mathcal{O}_S^\times$
   (NSW (8.3.5)–(8.3.13), including (8.3.11) on $H^i(G_S, \mathcal{O}_S^\times)$ and (8.3.13), the divisibility of
   the group $D_S$; Milne, Lemma I.4.1, Propositions I.4.2–4.3, Lemmas I.4.4–4.5), and that $(G_S, C_S)$ is a class
   formation for the primes in $\mathbb{N}(S)$ (NSW (8.3.9); Milne, Proposition I.4.2);
3. the global duality theorem for $\operatorname{Mod}_S(G_S)$ (NSW (8.4.1)–(8.4.5); Milne, Theorem I.4.6 and
   Corollary I.4.7);
4. the local cohomology of global modules: the topologies on the local and global groups, the isomorphisms
   $\Xi^i \colon P^i(G_S, A) \cong P^{2-i}(G_S, A')^\vee$ for finite $A$ (NSW (8.5.2), which rests on the
   unramified subgroups being exact annihilators), and the Shapiro maps $\mathrm{sh}^i$ (NSW (8.5.1)–(8.5.5));
5. the lemmas (8.6.3)–(8.6.6): the description $\text{Ш}^1(G_S, \mathbb{Z}/m\mathbb{Z}) \cong \operatorname{Hom}(\mathrm{Cl}_S(F), \mathbb{Z}/m\mathbb{Z})$
   and $\text{Ш}^1(G_S, \mathbb{Z}') \cong \mathrm{Cl}_S(F)$ by class field theory and Hilbert's Theorem 90 (8.6.3);
   the boundary map $C_S(A)^{G_S} \to H^1(G_S, A')$ and the finiteness of $\text{Ш}^1(G_S, A')$ (8.6.4), whose proof
   uses class field theory together with the **principal ideal theorem**, which needs its own page; the kernel of
   $\xi^i = \Xi^i \circ \lambda^i$ (8.6.5); and the compatibility diagrams (8.6.6); Milne, Lemmas I.4.8–4.9;
6. the Galois module structure of the $S$-units used by the global Euler characteristic formula (NSW (8.7.1)–(8.7.3)).

## Proof depends on

- [Fundamental class of a finite Galois extension of number fields](../../adeles-class-field-theory/reciprocity-law/fundamental-class.md), for the class formation of the idèle classes and their invariant maps, from which item 2 builds that of the $S$-idèle classes
- [S-unit theorem](../../discriminants-ramification/s-unit-theorem.md), for the finite generation and rank of the $S$-units used in items 2 and 6
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md), for the local duality in items 4 and 5
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the exact annihilators behind (8.5.2) in item 4
- [Tate duality for the real numbers](../galois-cohomology-of-local-fields/tate-duality-for-the-real-numbers.md), for the archimedean places in items 3 and 4
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the abstract duality relative to a class formation (Tate–Nakayama) used in item 3

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VIII, §3 (8.3.4)–(8.3.13),
  §4 (8.4.1)–(8.4.5), §5 (8.5.1)–(8.5.5), §6 (8.6.3)–(8.6.6) (the principal ideal theorem in the proof of (8.6.4),
  p. 482), §7 (8.7.1)–(8.7.3).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §4, Lemma 4.1 to Lemma 4.9.
