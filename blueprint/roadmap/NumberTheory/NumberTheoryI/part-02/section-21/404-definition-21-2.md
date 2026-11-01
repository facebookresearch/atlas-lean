---
article_id: af_0b21e4d4cac0b36eb9bdb439
declaration: structure
origin: cited
statement: formalized
lean: RayClassField.Modulus
---

# Definition 21.2

Let $K$ be a number field. A modulus (or cycle) $\mathfrak{m}$ for $K$ is a function $M_{K} \to \mathbb{Z}_{\geq 0}$ with finite support such that for $v \mid \infty$ we have $\mathfrak{m}(v) \leq 1$ with $\mathfrak{m}(v) = 0$ unless $v$ is a real place. We view $\mathfrak{m}$ as a formal product $\prod v^{\mathfrak{m}(v)}$ over $M_{K}$, which we may factor as $\mathfrak{m} = \mathfrak{m}_{0}\mathfrak{m}_{\infty}$, where $\mathfrak{m}_{0} \coloneqq \prod_{\mathfrak{p} \nmid \infty} \mathfrak{p}^{\mathfrak{m}(\mathfrak{p})}$ is an $\mathcal{O}_{K}$-ideal and $\mathfrak{m}_{\infty} \coloneqq \prod_{v \mid \infty} v^{\mathfrak{m}(v)}$ represents a subset of the real places of $K$. Divisibility, product, gcd, and lcm of moduli are defined componentwise (with the constraint that $\mathfrak{m}\mathfrak{n}(v) \coloneqq \max(\mathfrak{m}(v)+\mathfrak{n}(v),1)$ for $v \mid \infty$). The zero function is the trivial modulus. Additionally: $\mathcal{I}_{K}^{\mathfrak{m}} \subseteq \mathcal{I}_{K}$ is the subgroup of fractional ideals coprime to $\mathfrak{m}$; $K^{\mathfrak{m}} \subseteq K^{\times}$ is the subgroup of elements $\alpha$ with $(\alpha) \in \mathcal{I}_{K}^{\mathfrak{m}}$; $K^{\mathfrak{m},1} \subseteq K^{\mathfrak{m}}$ is the subgroup of $\alpha \in K^{\mathfrak{m}}$ with $v_{\mathfrak{p}}(\alpha - 1) \geq v_{\mathfrak{p}}(\mathfrak{m}_{0})$ for all $\mathfrak{p} \mid \mathfrak{m}_{0}$ and $\alpha_{v} > 0$ for $v \mid \mathfrak{m}_{\infty}$; $\mathcal{R}_{K}^{\mathfrak{m}} \subseteq \mathcal{I}_{K}^{\mathfrak{m}}$ is the subgroup of principal fractional ideals $(\alpha)$ with $\alpha \in K^{\mathfrak{m},1}$. The groups $\mathcal{R}_{K}^{\mathfrak{m}}$ are called rays or ray groups.

## Depends on

- [Definition 1.26](../../part-01/section-1/section-1/021-definition-1-26.md)
- [Definition 13.1](../../part-01/section-13/264-definition-13-1.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 21.3](../../../../../sources/v1/NumberTheoryI.md)
