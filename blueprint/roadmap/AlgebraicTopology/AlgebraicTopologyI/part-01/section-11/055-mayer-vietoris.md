---
article_id: af_1959e921cb3413d5f4252cf6
declaration: def
origin: cited
statement: formalized
lean: MayerVietoris.mayer_vietoris_sequence
---

# Theorem 11.5 (Mayer-Vietoris)

Assume that $\mathcal{A} = \{A, B\}$ is a cover of $X$. There are natural maps $\partial \colon H_{n}(X) \rightarrow H_{n-1}(A \cap B)$ such that the sequence $\cdots \rightarrow H_{n}(A \cap B) \xrightarrow{\alpha} H_{n}(A) \oplus H_{n}(B) \xrightarrow{\beta} H_{n}(X) \xrightarrow{\partial} H_{n-1}(A \cap B) \rightarrow \cdots$ is exact, where $\alpha = \begin{bmatrix} j_{1*} \\ -j_{2*} \end{bmatrix}$ and $\beta = \begin{bmatrix} i_{1*} & i_{2*} \end{bmatrix}$.

## Depends on

- [Definition 11.1](051-definition-11-1.md)
- [Definition 1.7](../chapter-1/chapter-1-section-1/007-definition-1-7.md)
- [Definition 3.5](../chapter-1/chapter-1-section-3/011-definition-3-5.md)
- [Definition 8.1](../section-8/034-definition-8-1.md)
- [Definition 11.2](052-definition-11-2.md)

## Proof depends on

- [Theorem 9.1 (The homology long exact sequence)](../section-9/039-the-homology-long-exact-sequence.md)
- [Theorem 10.2](../section-10/044-theorem-10-2.md)
- [Theorem 11.4 (The locality principle)](054-the-locality-principle.md)
- [Lemma 11.6](056-lemma-11-6.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Section 11, The Eilenberg Steenrod axioms and the locality principle](../../../../../sources/v1/AlgebraicTopologyI.md)
