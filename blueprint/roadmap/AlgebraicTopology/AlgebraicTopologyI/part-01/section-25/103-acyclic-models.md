---
article_id: af_e5318dbdeb5a7489d036dd98
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: AcyclicModels.acyclic_models
---

# Theorem 25.11 (Acyclic Models)

Let $\mathcal{M}$ be a set of models in a category $\mathcal{C}$. Let $\theta \colon F \rightarrow G$ be a natural transformation of functors from $\mathcal{C}$ to $\mathbf{Ab}$. Let $F_{*}$ and $G_{*}$ be functors from $\mathcal{C}$ to chain complexes, with augmentations $F_{0} \rightarrow F$ and $G_{0} \rightarrow G$. Assume that $F_{n}$ is $\mathcal{M}$-free for all $n$, and that $G_{*} \rightarrow G \rightarrow 0$ is an $\mathcal{M}$-exact sequence. Then there is a unique chain homotopy class of chain maps $F_{*} \rightarrow G_{*}$ covering $\theta$.

## Depends on

- [Definition 25.4](100-definition-25-4.md)
- [Definition 3.4](../chapter-1/chapter-1-section-3/010-definition-3-4.md)
- [Definition 3.5](../chapter-1/chapter-1-section-3/011-definition-3-5.md)
- [Definition 5.9](../chapter-1/chapter-1-section-5/025-definition-5-9.md)

## Proof depends on

- [Definition 25.7](101-definition-25-7.md)
- [Lemma 25.10](102-lemma-25-10.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Section 25](../../../../../sources/v1/AlgebraicTopologyI.md)
