---
article_id: af_11408af1099b1d70d6ed2b2b
declaration: abbrev
origin: cited
statement: formalized
lean: Definition_1_20_2
---

# Definition 1.20.2

A left comodule over a coalgebra $C$ is a vector space $M$ together with a linear map $\pi \colon M \to C \otimes M$ (called the coaction map), such that for any $m \in M$, one has $(\Delta \otimes \operatorname{Id})(\pi(m)) = (\operatorname{Id} \otimes \pi)(\pi(m))$, $(\varepsilon \otimes \operatorname{Id})(\pi(m)) = m$. Similarly, a right comodule over $C$ is a vector space $M$ together with a linear map $\pi \colon M \to M \otimes C$, such that for any $m \in M$, one has $(\pi \otimes \operatorname{Id})(\pi(m)) = (\operatorname{Id} \otimes \Delta)(\pi(m))$, $(\operatorname{Id} \otimes \varepsilon)(\pi(m)) = m$.

## Depends on

- [Definition 1.20.1](049-definition-1-20-1.md)

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 1.20](../../../../../../sources/v1/TensorCategories.md)
