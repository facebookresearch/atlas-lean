---
article_id: af_c6298b3fd115be9f58bdc832
declaration: abbrev
origin: cited
statement: formalized
lean: DerivedFunctor.CochainComplexRMod
---

# Definition 23.53

A cochain complex $C$ is a sequence of $R$-module morphisms $0 \longrightarrow C^{0} \xrightarrow{d^{0}} C^{1} \xrightarrow{d^{1}} C^{2} \xrightarrow{d^{2}} \cdots$ with $d^{n+1} \circ d^{n}=0$. The $n$th cohomology group of $C$ is the $R$-module $H^{n}(C)\coloneqq Z^{n}(C)/B^{n}(C)$, where $Z^{n}(C)\coloneqq \ker d^{n}$ and $B^{n}(C)\coloneqq \operatorname{im} d^{n-1}$ are the $R$-modules of cocycles and coboundaries; for $n<0$ we define $C^{n}=0$ and $d^{n}$ is the zero map. A morphism of cochain complexes $f: C \rightarrow D$ consists of $R$-module morphisms $f^{n}: C^{n} \rightarrow D^{n}$ that commute with coboundary maps, yielding natural morphisms $H^{n}(f): H^{n}(C) \rightarrow H^{n}(D)$ and functors $H^{n}(\bullet)$ from the category of cochain complexes to the category of abelian groups. Morphisms of cochain complexes $f, g: C \rightarrow D$ are homotopic if there are morphisms $h^{n}: C^{n+1} \rightarrow D^{n}$ such that $f^{n}-g^{n}=h^{n} \circ d^{n}+d^{n-1} \circ h^{n-1}$ for all $n \geq 0$ (where $h^{-1}\coloneqq 0$); this defines an equivalence relation $f \sim g$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 23.7, Subsection 23.7.1](../../../../../../sources/v1/NumberTheoryI.md)
