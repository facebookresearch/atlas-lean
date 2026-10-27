---
article_id: af_05462207ba6fea32a4ee2cdb
declaration: abbrev
origin: cited
statement: formalized
lean: TensorCategories.Definition_1_46_1
---

# Definition 1.46.1

Deligne's tensor product $\mathcal{C} \boxtimes \mathcal{D}$ is an abelian category which is universal for the functor assigning to every $k$-linear abelian category $\mathcal{A}$ the category of right exact in both variables bilinear bifunctors $\mathcal{C} \times \mathcal{D} \rightarrow \mathcal{A}$. That is, there is a bifunctor $\boxtimes: \mathcal{C} \times \mathcal{D} \rightarrow \mathcal{C} \boxtimes \mathcal{D}: (X, Y) \mapsto X \boxtimes Y$ which is right exact in both variables and is such that for any right exact in both variables bifunctor $F: \mathcal{C} \times \mathcal{D} \rightarrow \mathcal{A}$ there exists a unique right exact functor $\bar{F}: \mathcal{C} \boxtimes \mathcal{D} \rightarrow \mathcal{A}$ satisfying $\bar{F} \circ \boxtimes = F$.

## Depends on

- [Definition 1.18.1](../../part-01/section-1-18/045-definition-1-18-1.md)

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 1.46](../../../../../../sources/v1/TensorCategories.md)
