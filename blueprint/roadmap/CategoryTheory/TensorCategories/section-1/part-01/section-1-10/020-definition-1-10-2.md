---
article_id: af_096a3c01358af6fd0f56cc41
declaration: abbrev
origin: cited
statement: formalized
lean: TensorCategories.Definition_1_10_2
---

# Definition 1.10.2

A left dual of an object $X$ in $\mathcal{C}$ is an object ${}^{*}X$ in $\mathcal{C}$ equipped with morphisms $\operatorname{ev}_{X}' \colon X \otimes {}^{*}X \to \mathbf{1}$ and $\operatorname{coev}_{X}' \colon \mathbf{1} \to {}^{*}X \otimes X$ such that the compositions $X \xrightarrow{\mathrm{Id}_{X} \otimes \operatorname{coev}_{X}'} X \otimes ({}^{*}X \otimes X) \xrightarrow{a_{X,{}^{*}X,X}^{-1}} (X \otimes {}^{*}X) \otimes X \xrightarrow{\mathrm{ev}_{X}' \otimes \mathrm{Id}_{X}} X$ and ${}^{*}X \xrightarrow{\operatorname{coev}_{X}' \otimes \mathrm{Id}_{{}^{*}X}} ({}^{*}X \otimes X) \otimes {}^{*}X \xrightarrow{a_{{}^{*}X,X,{}^{*}X}} {}^{*}X \otimes (X \otimes {}^{*}X) \xrightarrow{\mathrm{Id}_{{}^{*}X} \otimes \mathrm{ev}_{X}'} {}^{*}X$ are the identity morphisms.

## Depends on

- [Definition 1.1.1](../section-1-1/001-definition-1-1-1.md)

## Sources

- [MIT 18.769 Topics in Lie Theory: Tensor Categories (Spring 2009), Section 1.10](../../../../../../sources/v1/TensorCategories.md)
