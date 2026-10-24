---
article_id: af_3a33174141b870cc44310bed
declaration: structure
origin: cited
statement: formalized
lean: ProjectiveRatMap.ProjectiveRationalMap
---

# Definition 15.14

Let $X \subseteq \mathbb{P}^m$ and $Y \subseteq \mathbb{P}^n$ be projective varieties. A rational map $\varphi \colon X \rightarrow Y$ is an equivalence class of tuples $\varphi = (\varphi_0 : \ldots : \varphi_n)$ with $\varphi_i \in \bar{k}(X)$ not all zero such that at any point $P \in X$ where all the $\varphi_i$ are regular and at least one is nonzero, the point $(\varphi_0(P) : \ldots : \varphi_n(P))$ lies in $Y$. The equivalence relation is given by $(\varphi_0 : \ldots : \varphi_n) = (\lambda\varphi_0 : \ldots : \lambda\varphi_n)$ for any $\lambda \in \bar{k}(X)^{\times}$. We say that $\varphi$ is regular at $P$ if there is a tuple $(\lambda\varphi_0 : \ldots : \lambda\varphi_n)$ in its class with each component regular at $P$ and at least one nonzero at $P$. The open subset of $X$ at which $\varphi$ is regular is denoted $\operatorname{dom}(\varphi)$.

## Depends on

- [Definition 13.4](../section-13/section-13-1/103-definition-13-4.md)
- [Definition 13.18](../section-13/section-13-4/115-definition-13-18.md)
- [Definition 15.13](141-definition-15-13.md)

## Sources

- [MIT 18.782 Introduction to Arithmetic Geometry (Fall 2013), Section 15.2](../../../../../sources/v1/ArithmeticGeometry.md)
