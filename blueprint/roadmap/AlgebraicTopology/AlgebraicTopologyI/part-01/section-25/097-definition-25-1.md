---
article_id: af_527b9b5224d35c5227215619
declaration: def
origin: cited
statement: formalized
lean: TensorChainComplex.tensorChainComplex
---

# Definition 25.1

Let $C_{*}, D_{*}$ be two chain complexes. Their tensor product is the chain complex with $(C_{*} \otimes D_{*})_{n} = \bigoplus_{p+q=n} C_{p} \otimes D_{q}$. The differential $(C_{*} \otimes D_{*})_{n} \rightarrow (C_{*} \otimes D_{*})_{n-1}$ sends $C_{p} \otimes D_{q}$ into the submodule $C_{p-1} \otimes D_{q} \oplus C_{p} \otimes D_{q-1}$ by $x \otimes y \mapsto dx \otimes y + (-1)^{p} x \otimes dy$.

## Depends on

- [Definition 1.6](../chapter-1/chapter-1-section-1/006-definition-1-6.md)
- [Definition 20.3](../section-20/080-definition-20-3.md)

## Sources

- [MIT 18.905 Algebraic Topology I (Fall 2016), Section 25](../../../../../sources/v1/AlgebraicTopologyI.md)
