---
article_id: af_9571f93ea3d011291aeeb3aa
declaration: abbrev
origin: cited
statement: formalized
lean: ChainComplexDef.ChainComplexRMod
---

# Definition 23.49

A chain complex $C$ is a sequence of $R$-module morphisms $\cdots \xrightarrow{d_{2}} C_{2} \xrightarrow{d_{1}} C_{1} \xrightarrow{d_{0}} C_{0} \longrightarrow 0$, with $d_{n} \circ d_{n+1}=0$; the $d_{n}$ are boundary maps. The $n$th homology group of $C$ is the $R$-module $H_{n}(C)\coloneqq Z_{n}(C)/B_{n}(C)$, where $Z_{n}(C)\coloneqq \ker d_{n-1}$ and $B_{n}(C)\coloneqq \operatorname{im} d_{n}$ are the $R$-modules of cycles and boundaries, respectively; for $n<0$ we define $C_{n}=0$ and $d_{n}$ is the zero map. A morphism of chain complexes $f: C \rightarrow D$ is a sequence of $R$-module morphisms $f_{n}: C_{n} \rightarrow D_{n}$ that commute with boundary maps (so $f_{n} \circ d_{n}=d_{n} \circ f_{n+1}$). Such a morphism necessarily maps cycles to cycles and boundaries to boundaries, yielding natural morphisms $H_{n}(f): H_{n}(C) \rightarrow H_{n}(D)$ of homology groups.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 23.7, Subsection 23.7.1](../../../../../../sources/v1/NumberTheoryI.md)
