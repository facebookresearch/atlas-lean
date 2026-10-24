---
article_id: af_92eaf650e027147039b5194d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MeasureTheory.measurableSpace_isSetAlgebra
---

# Definition (March 11, 2021)

A nonempty collection of sets $\mathcal{A} \subset \mathcal{P}(\mathbb{R})$ is an algebra (not the same as the "algebra" in algebra) if for all $E \in \mathcal{A}$, we have $E^c \in \mathcal{A}$, and for all $E_1, \cdots, E_n \in \mathcal{A}$, we have $\bigcup_{k=1}^n E_k \in \mathcal{A}$. Furthermore, an algebra $\mathcal{A}$ is a $\sigma$-algebra if we have the additional condition that for any countable collection $\{E_n\}_{n=1}^\infty$ of sets in $\mathcal{A}$, the union $\bigcup_n E_n$ is also in the algebra.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), March 11, 2021](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
