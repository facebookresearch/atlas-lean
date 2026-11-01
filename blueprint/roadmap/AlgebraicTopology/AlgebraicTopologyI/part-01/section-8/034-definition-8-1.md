---
article_id: af_9b08d100e0ae3c9fd79cbb19
declaration: structure
origin: cited
statement: formalized
lean: ExactSequence.IntChainComplex
---

# Definition 8.1

A sequence of abelian groups is a diagram of abelian groups of the form $\cdots \rightarrow C_{n+1} \xrightarrow{f_{n}} C_{n} \xrightarrow{f_{n-1}} C_{n-1} \rightarrow \cdots$, in which all composites are zero; that is, $\operatorname{im} f_{n} \subseteq \operatorname{ker} f_{n-1}$ for all $n$. It is exact at $C_{n}$ provided that this inequality is an equality.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Section 8, Relative homology](../../../../../sources/v1/AlgebraicTopologyI.md)
