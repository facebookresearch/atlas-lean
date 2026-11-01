---
article_id: af_c50adb3ab651c422f04f5da5
declaration: abbrev
origin: cited
statement: formalized
lean: TopologicalSpace.DirectLimit.Space
---

# Definition 25.4

Let $(X_i, f_{ij})$ be a direct system of topological spaces. The direct limit (or inductive limit) of $(X_i, f_{ij})$ is the quotient space $X = \varinjlim X_i \coloneqq \coprod_{i \in I} X_i / \sim$, where $x_i \sim f_{ij}(x_i)$ for all $i \leq j$. It is equipped with continuous maps $\phi_i: X_i \rightarrow X$ that are compositions of the inclusion maps $X_i \hookrightarrow \coprod X_i$ and quotient maps $\coprod X_i \rightarrow \coprod X_i / \sim$ and satisfy $\phi_i = \phi_j \circ f_{ij}$ for $i \leq j$.

## Depends on

- [Definition 25.3](529-definition-25-3.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 25.2](../../../../../sources/v1/NumberTheoryI.md)
