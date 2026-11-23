# Local class field theory: functoriality and explicit reciprocity

This node is still to be broken down. It covers the properties of
[the local Artin map](local-class-field-theory.md) $\mathrm{rec}_K$ beyond its definition that the global
theory uses: its behaviour under norms, its expression by cup products, and its explicit value on the
cyclotomic extensions of $\mathbb{Q}_p$. Let $K$ be a non-archimedean local field of characteristic $0$.
It contains the following statements.

1. **Norm functoriality.** For a tower $L \supseteq E \supseteq K$ with $L/K$ finite Galois, the local Artin
   map of $L/E$ followed by the map $\mathrm{Gal}(L/E)^{\mathrm{ab}} \to \mathrm{Gal}(L/K)^{\mathrm{ab}}$ induced
   by the inclusion equals the local Artin map of $L/K$ composed with $\mathrm{Nm}_{E/K}$ (Milne, Lemma
   III.3.2, whose proof Milne defers). In particular, for every finite extension $K'/K$ and every finite
   abelian extension $M/K$, $\mathrm{rec}_{K'}(b)|_M = \mathrm{rec}_K(\mathrm{Nm}_{K'/K}(b))$ for all
   $b \in K'^\times$.
2. **The cup-product formula.** For a finite abelian extension $L/K$ with group $G$, every
   $\chi \in \mathrm{Hom}(G, \mathbb{Q}/\mathbb{Z})$ and every $a \in K^\times$,
   $\chi(\mathrm{rec}_{L/K}(a)) = \mathrm{inv}_K(a \cup \delta\chi)$, where
   $\delta \colon H^1(G, \mathbb{Q}/\mathbb{Z}) \to H^2(G, \mathbb{Z})$ is the connecting map of
   $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$, $a \cup \delta\chi \in H^2(G, L^\times)$ and
   $\mathrm{inv}_K$ is the local invariant map (Milne, Proposition III.3.6, which refers to Serre).
3. **Explicit reciprocity for cyclotomic extensions of $\mathbb{Q}_p$.** For $a = u p^t$ with
   $u \in \mathbb{Z}_p^\times$ and $t \in \mathbb{Z}$, $\mathrm{rec}_{\mathbb{Q}_p}(a)$ acts on the $p^r$-th
   roots of unity as $\zeta \mapsto \zeta^{u_0^{-1}}$, where $u_0 \in \mathbb{Z}$ is congruent to $u$
   modulo $p^r$, and on the roots of unity of order prime to $p$ as the $t$-th power of the Frobenius
   (Milne, Example I.3.13, from Lubin–Tate theory, Sections I.2–I.3).

A good expansion has a page for each numbered item; the third needs pages for the Lubin–Tate formal groups
and the extensions they generate (Milne, Sections I.2 and I.3).

## Depends on

- [Local class field theory: the local Artin map](local-class-field-theory.md)
- [Local class field theory: cohomology and the existence theorem](local-class-field-theory-cohomology.md), for the local invariant map in item 2 (its item 2)

## Proof depends on

- [Restriction, corestriction, inflation and Tate's theorem in group cohomology](../../RepresentationTheory/group-cohomology/restriction-corestriction-inflation-and-tate-s-theorem.md), for cup products and their compatibility with restriction and corestriction, in items 1 and 2

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: Lemma III.3.2 and 3.3, Proposition III.3.6;
  Example I.3.13 with Sections I.2 and I.3 (Lubin–Tate theory).
