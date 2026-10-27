---
article_id: af_f2d0c19ed4d128da46800f2d
declaration: def
origin: cited
statement: formalized
lean: def_15_3_size
---

# Definition 15.3

Let $K$ be a global field. The size of an Arakelov divisor $c$ is $\|c\| \coloneqq \prod_{v \in M_K} c_v \in \mathbb{R}_{>0}$. The map $\operatorname{Div} K \to \mathbb{R}_{>0}^\times$ defined by $c \mapsto \|c\|$ is a group homomorphism whose kernel contains $\operatorname{Princ} K$ (by the product formula). Corresponding to each Arakelov divisor $c$ is a subset $L(c)$ of $K$ defined by $L(c) \coloneqq \{x \in K : \|x\|_v \leq c_v \text{ for all } v \in M_K\}$, and a nonzero fractional ideal of $\mathcal{O}_K$ defined by $I_c \coloneqq \prod_{v \nmid \infty} \mathfrak{q}_v^{v(c)}$, where $\mathfrak{q}_v \coloneqq \{a \in \mathcal{O}_K : v(a) > 0\}$ is the prime ideal corresponding to the discrete valuation $v$ that induces $\|\cdot\|_v$, and $v(c) \coloneqq -\log_{\# k_v}(c_v) \in \mathbb{Z}$. We have $L(c) \subseteq I_c \subseteq K$, and the map $c \mapsto I_c$ defines a group homomorphism $\operatorname{Div} K \to \mathcal{I}_K$.

## Depends on

- [Definition 2.13](../section-2/029-definition-2-13.md)
- [Definition 13.17](../section-13/276-definition-13-17.md)
- [Definition 13.22](../section-13/279-definition-13-22.md)
- [Definition 15.1](304-definition-15-1.md)

## Proof depends on

- [Theorem 13.21 (Product Formula)](../section-13/278-product-formula.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 15.1](../../../../../sources/v1/NumberTheoryI.md)
