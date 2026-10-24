---
article_id: af_e52bdad7f37a732e43ce077f
declaration: structure
origin: cited
statement: formalized
lean: EilenbergSteenrod.HomologyTheory
---

# Definition 11.1

A homology theory (on $\mathbf{Top}$) is: a sequence of functors $h_{n} \colon \mathbf{Top}_{2} \rightarrow \mathbf{Ab}$ for all $n \in \mathbb{Z}$ and a sequence of natural transformations $\partial \colon h_{n}(X, A) \rightarrow h_{n-1}(A, \varnothing)$ such that: (1) If $f_{0}, f_{1} \colon (X, A) \rightarrow (Y, B)$ are homotopic, then $f_{0*} = f_{1*} \colon h_{n}(X, A) \rightarrow h_{n}(Y, B)$. (2) Excisions induce isomorphisms. (3) For any pair $(X, A)$, the sequence $\cdots \rightarrow h_{q+1}(X, A) \xrightarrow{\partial} h_{q}(A) \rightarrow h_{q}(X) \rightarrow h_{q}(X, A) \xrightarrow{\partial} \cdots$ is exact. (4) The dimension axiom: The group $h_{n}(*)$ is nonzero only for $n = 0$. Additionally, the Milnor axiom: the map $\alpha \colon \bigoplus_{i \in I} h_{n}(X_{i}) \rightarrow h_{n}(\coprod_{i \in I} X_{i})$ induced by the inclusion maps is an isomorphism for all $n$.

## Depends on

- [Definition 3.4](../chapter-1/chapter-1-section-3/010-definition-3-4.md)
- [Definition 3.5](../chapter-1/chapter-1-section-3/011-definition-3-5.md)
- [Definition 5.1](../chapter-1/chapter-1-section-5/017-definition-5-1.md)
- [Definition 8.1](../section-8/034-definition-8-1.md)
- [Definition 10.1](../section-10/043-definition-10-1.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Section 11, The Eilenberg Steenrod axioms and the locality principle](../../../../../sources/v1/AlgebraicTopologyI.md)
