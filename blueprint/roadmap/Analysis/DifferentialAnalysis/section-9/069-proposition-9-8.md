---
article_id: af_1b9f6bc10e8609154ee21f57
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SobolevHilbert.proposition_9_8
---

# Proposition 9.8

Each of the Sobolev spaces $H^m(\mathbb{R}^n)$ is a Hilbert space with the norm and inner product $\|u\|_{H^m} = \left(\int_{\mathbb{R}^n} |\hat{u}(\xi)|^2 \langle\xi\rangle^{2m}\, d\xi\right)^{1/2}$ and $\langle u, v\rangle = \int_{\mathbb{R}^n} \hat{u}(\xi) \overline{\hat{v}(\xi)} \langle\xi\rangle^{2m}\, d\xi$. The Schwartz space $\mathcal{S}(\mathbb{R}^n) \hookrightarrow H^m(\mathbb{R}^n)$ is dense for each $m$ and the pairing $H^m(\mathbb{R}^n) \times H^{-m}(\mathbb{R}^n) \ni (u, u') \longmapsto ((u, u')) = \int_{\mathbb{R}^n} \hat{u}(\xi) \overline{\hat{u}'(\xi)}\, d\xi \in \mathbb{C}$ gives an identification $(H^m(\mathbb{R}^n))' = H^{-m}(\mathbb{R}^n)$.

## Depends on

- [Definition 5.1](../section-5/034-definition-5-1.md)
- [Definition 6.6](../section-6/043-definition-6-6.md)

## Proof depends on

- [Corollary 5.4](../section-5/037-corollary-5-4.md)
- [Theorem 9.1](062-theorem-9-1.md)

## Sources

- [MIT 18.155 Differential Analysis (Fall 2004), Section 9](../../../../sources/v1/DifferentialAnalysis.md)
