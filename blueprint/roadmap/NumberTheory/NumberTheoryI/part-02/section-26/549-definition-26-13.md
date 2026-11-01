---
article_id: af_5cd69d7da3f53384948ddbb9
declaration: class
origin: cited
statement: formalized
lean: Ideles.IsProfiniteGroup
---

# Definition 26.13

A profinite group is a topological group that is an inverse limit of finite groups with the discrete topology. Given any topological group $G$, we can construct a profinite group by taking the profinite completion $\widehat{G}\coloneqq \varprojlim_{N} G / N \subseteq \prod_{N} G / N$ where $N$ ranges over finite index open normal subgroups, ordered by containment. If we are given a group $G$ without a specified topology, we can make it a topological group by giving it the profinite topology. This is the weakest topology that makes every finite quotient discrete and is obtained by taking all cosets of finite-index normal subgroups as a basis.

## Depends on

- [Definition 8.9](../../part-01/section-8/180-definition-8-9.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 26.2](../../../../../sources/v1/NumberTheoryI.md)
