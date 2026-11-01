---
article_id: af_e408e606a419e471f0860fa7
declaration: abbrev
origin: cited
statement: formalized
lean: TensorCategories.Definition_1_10_1
---

# Definition 1.10.1

A right dual of an object $X$ in $\mathcal{C}$ is an object $X^{*}$ in $\mathcal{C}$ equipped with morphisms $\mathrm{ev}_{X} \colon X^{*} \otimes X \to \mathbf{1}$ and $\operatorname{coev}_{X} \colon \mathbf{1} \to X \otimes X^{*}$, called the evaluation and coevaluation morphisms, such that the compositions $X \xrightarrow{\operatorname{coev}_{X} \otimes \operatorname{Id}_{X}} (X \otimes X^{*}) \otimes X \xrightarrow{a_{X, X^{*}, X}} X \otimes (X^{*} \otimes X) \xrightarrow{\operatorname{Id}_{X} \otimes \operatorname{ev}_{X}} X$ and $X^{*} \xrightarrow{\operatorname{Id}_{X^{*}} \otimes \operatorname{coev}_{X}} X^{*} \otimes (X \otimes X^{*}) \xrightarrow{a_{X^{*}, X, X^{*}}^{-1}} (X^{*} \otimes X) \otimes X^{*} \xrightarrow{\operatorname{ev}_{X} \otimes \operatorname{Id}_{X^{*}}} X^{*}$ are the identity morphisms.

## Depends on

- [Definition 1.1.1](../section-1-1/001-definition-1-1-1.md)

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 1.10](../../../../../../sources/v1/TensorCategories.md)
