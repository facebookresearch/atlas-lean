---
article_id: af_87d5fd87b1bb9304b1762757
declaration: structure
origin: cited
statement: formalized
lean: InverseLimit.NatInverseSystem
---

# Definition 4.1

An inverse system is a sequence of objects (e.g. sets/groups/rings) $(A_{n})$ together with a sequence of morphisms (e.g. functions/homomorphisms) $(f_{n})$ $$\cdots \longrightarrow A_{n+1} \xrightarrow{f_{n}} A_{n} \longrightarrow \cdots \longrightarrow A_{2} \xrightarrow{f_{1}} A_{1}.$$ The inverse limit $$A=\varprojlim A_{n}$$ is the subset of the direct product $\prod_{n} A_{n}$ consisting of those sequences $a=(a_{n})$ for which $f_{n}(a_{n+1})=a_{n}$ for all $n \geq 1$. For each $n \geq 1$ the projection map $\pi_{n}: A \rightarrow A_{n}$ sends $a$ to $a_{n}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.782 Introduction to Arithmetic Geometry (Fall 2013), Section 4.1](../../../../../sources/v1/ArithmeticGeometry.md)
