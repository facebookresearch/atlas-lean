---
article_id: af_7a170f044605970c2c047c68
declaration: abbrev
origin: cited
statement: formalized
lean: HilbertSpace.PreHilbertSpace
---

# Definition (Pre-Hilbert space)

A pre-Hilbert space $H$ is a vector space over $\mathbb{C}$ with a Hermitian inner product, which is a map $\langle \cdot, \cdot \rangle: H \times H \to \mathbb{C}$ satisfying the following properties: (1) For all $\lambda_1, \lambda_2 \in \mathbb{C}$ and $v_1, v_2, w \in H$, we have $\langle \lambda_1 v_1 + \lambda_2 v_2, w \rangle = \lambda_1 \langle v_1, w \rangle + \lambda_2 \langle v_2, w \rangle$, (2) For all $v, w \in H$, we have $\langle v, w\rangle = \overline{\langle w, v \rangle}$, (3) For all $v \in H$, we have $\langle v, v \rangle \geq 0$, with equality if and only if $v = 0$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), April 6, 2021 section](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
