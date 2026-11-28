# Exactness of the Poitou–Tate complex

This node is still to be broken down. It covers the steps through which Neukirch–Schmidt–Wingberg prove the
[Poitou–Tate exact sequence](poitou-tate-exact-sequence.md) and the
[global Euler characteristic formula](global-euler-characteristic-formula.md) once the finiteness theorems and
Poitou–Tate duality are known. Let $F$ be a number field, $S \supseteq S_\infty$ a set of places of $F$, $G_S$ the
Galois group of the maximal extension of $F$ unramified outside $S$, and $A$ a finite $G_S$-module of order in
$\mathbb{N}(S)$, with $A' = \operatorname{Hom}(A, \mu)$. These steps use
[finiteness and cohomological dimension of $G_S$](finiteness-and-cohomological-dimension-of-g-s.md) and
[Poitou–Tate duality](poitou-tate-duality.md), so they are kept apart from the earlier results gathered in the
node on [global duality for Galois groups with restricted ramification](global-duality-for-galois-groups-with-restricted-ramification.md).

A good expansion has pages for:

1. the properness of the localization map $\lambda^1 \colon H^1(G_S, A) \to P^1(G_S, A)$ for
   $A \in \operatorname{Mod}_S(G_S)$ (NSW (8.6.11));
2. the exact sequence $0 \to H^0(G_S, A') \to P^0(G_S, A') \to H^2(G_S, A)^\vee \to \text{Ш}^1(G_S, A') \to 0$ for
   finite $A$, with its diagram (NSW (8.6.12)), whose proof passes to countable towers of finite extensions by the
   results of Chapter II, §7, and uses the norm-one $S$-idèle classes $C_S^0$;
3. the Euler characteristic quotient $\varphi(G_S, A)$ for finite $S$: $\varphi(G_S, A) \cdot \varphi(G_S, A') = 1$ if
   and only if the Poitou–Tate complex is exact, and $\varphi(G_S, -)$ is multiplicative on short exact sequences
   (NSW (8.6.13)). The first part uses the product formula and the local Euler characteristic formula. The second
   does not use any vanishing in degrees at least $3$, which fails in general: it uses the isomorphisms
   $H^i(G_S, A) \cong \bigoplus_{v \text{ real}} H^i(F_v, A)$ for $i \ge 3$ of (8.6.10)(ii) (for $F = \mathbb{Q}$,
   $S = \{2, \infty\}$ and $A = \mathbb{Z}/2\mathbb{Z}$, $H^3(G_S, A) \cong H^3(\mathbb{R}, A) \cong \mathbb{Z}/2\mathbb{Z}$), keeps the
   resulting real-place terms $P^3$ and $P^4$ in the count, compares them by the triviality of the Herbrand quotient
   of finite modules (NSW (1.7.6)), and uses the exact sequences of the groups $H^0(F_v, -)$ at the archimedean places;
4. the base cases of the proof of (8.6.10)(i): exactness of the Poitou–Tate complex for $A = \mathbb{Z}/p\mathbb{Z}$ and
   $A = \mu_p$ with $p \in \mathbb{N}(S)$ (Step 1). The case $\mu_p$ uses the sequence
   $0 \to \mu_p \to {}_p I_S \to {}_p C_S \to 0$ given by (8.3.4), $H^1(G_S, C_S) = 0$ (8.3.9), the local comparison
   (7.2.13) of the cup product $H^1(F_v, \mu_p) \times H^1(F_v, \mathbb{Z}/p\mathbb{Z}) \to H^2(F_v, \mu_p)$ with the local
   reciprocity map, through the Kummer map $F_v^\times/F_v^{\times p} \cong H^1(F_v, \mu_p)$, which makes the localization
   of $H^1(G_S, \mu_p)$ anti-commute with the local reciprocity maps, and then the global reciprocity isomorphism
   $C_S(F)/p \cong G_S^{\mathrm{ab}}/p$, which rests on the divisibility of the group $D_S$ (8.3.13). The reduction steps
   pass from these cases to all finite $A$ (Steps 2–5): from finite subsets of $S$ by the properness of item 1
   (Step 2), along short exact sequences by item 3 (Step 3), to modules killed by $p$ and trivialized by a
   $p$-extension through a composition series with factors $\mathbb{Z}/p\mathbb{Z}$ (NSW (1.6.13); Step 4), and to all
   finite $A$ by restriction and corestriction along the field fixed by a $p$-Sylow subgroup (Step 5).

## Depends on

- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md), for $G_S$, $\mathbb{N}(S)$, $\operatorname{Mod}_S(G_S)$, the dual $A'$, the restricted products $P^i$ and the localization maps $\lambda^i$
- [Tate–Shafarevich groups of Galois modules](tate-shafarevich-groups.md), for $\text{Ш}^1(G_S, A')$ in item 2
- [Finiteness and cohomological dimension of Galois groups with restricted ramification](finiteness-and-cohomological-dimension-of-g-s.md), for the finiteness of the groups, which defines the Euler characteristic quotient $\varphi(G_S, A)$ of item 3
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md), for the isomorphisms $P^i(G_S, A) \cong P^{2-i}(G_S, A')^\vee$ at the non-archimedean places, through which the maps $P^i \to H^{2-i}(G_S, -)^\vee$ of items 2 and 3 are defined
- [Tate duality for the real numbers](../galois-cohomology-of-local-fields/tate-duality-for-the-real-numbers.md), for those isomorphisms at the archimedean places
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the unramified subgroups as exact annihilators, which make the local dualities an isomorphism of restricted products
- [Poitou–Tate duality](poitou-tate-duality.md), for the maps $H^{2-i}(G_S, A')^\vee \to H^{i+1}(G_S, A)$ of the Poitou–Tate complex in item 3

## Proof depends on

- [Finiteness and cohomological dimension of Galois groups with restricted ramification](finiteness-and-cohomological-dimension-of-g-s.md), for the finiteness of the groups (items 3 and 4) and the isomorphisms $H^i(G_S, A) \cong \bigoplus_{v \text{ real}} H^i(F_v, A)$ for $i \ge 3$ (item 3)
- [Herbrand quotients agree across a map with finite kernel and cokernel](../../../../RepresentationTheory/group-cohomology/tate-cohomology-and-the-herbrand-quotient/herbrand-quotient-finite-kernel-cokernel.md), for the triviality of the Herbrand quotient of a finite module over $\operatorname{Gal}(\mathbb{C}/\mathbb{R})$, which gives $\# P^3 = \# P^4$ in item 3
- [Poitou–Tate duality](poitou-tate-duality.md), used in items 2 and 4
- [Global duality for Galois groups with restricted ramification](global-duality-for-galois-groups-with-restricted-ramification.md), for the global duality theorem, the maps $\Xi^i$ and the Shapiro maps, and the divisibility of $D_S$
- [Global reciprocity law](../../adeles-class-field-theory/reciprocity-law/global-reciprocity-law.md), for the global reciprocity map in the base case $\mu_p$ of item 4
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the cup-product formula $\chi(\mathrm{rec}(a)) = \mathrm{inv}(a \cup \delta\chi)$ (its item 3), from which NSW derive the local comparison (7.2.12)–(7.2.13) used in the base case $\mu_p$ of item 4
- [Galois cohomology of roots of unity over a p-adic field](../galois-cohomology-of-local-fields/cohomology-of-roots-of-unity-over-p-adic-fields.md), for the Kummer map in that local comparison
- [Product formula for principal ideles](../../adeles-class-field-theory/adeles-and-ideles/adelic-norm-principal-embedding.md), for $\prod_v \lVert \# A \rVert_v = 1$ in item 3
- [Local Euler characteristic formula](../galois-cohomology-of-local-fields/local-euler-characteristic-formula.md), used in item 3
- [Continuous cohomology of a countable inverse limit of finite modules](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/continuous-cochain-cohomology/continuous-cohomology-of-a-countable-inverse-limit.md) and [continuous cohomology as an inverse limit over finite levels](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/continuous-cochain-cohomology/continuous-cohomology-as-an-inverse-limit.md), for continuous cohomology along countable towers in item 2
- [Inflation, restriction and conjugation](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/change-of-group/inflation-restriction-and-conjugation.md) and [Corestriction for open subgroups](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/change-of-group/corestriction.md), for restriction and corestriction in item 4
- [Simple modules over pro-p-groups](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/simple-modules-over-pro-p-groups.md), for the composition series of item 4

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VIII, §6, (8.6.11)
  Proposition, (8.6.12) Lemma, (8.6.13) Lemma with its proof (using (7.3.1), (7.3.5), (8.6.10)(ii) and (1.7.6)), and the
  proof of (8.6.10)(i), Steps 1–5 (Step 1 through (8.3.4), (8.3.9), (7.2.13) and (8.3.13)), pp. 491–500; Chapter VII,
  (7.2.12)–(7.2.13), p. 386.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Lemmas 4.12–4.13 and the proof of Theorem 4.10, and §5, the proof of Theorem 5.1.
