---
article_id: af_b8e2c02928e9c2cfa560d164
declaration: theorem
origin: cited
lean: Martingales.azuma_inequality_alt
---

# Theorem 9.2.8 (Azuma's inequality)

Let $Z_0, Z_1, \ldots, Z_n$ be a martingale satisfying $|Z_i - Z_{i-1}| \leq c_i$ for each $i \in [n]$. For any $\lambda > 0$, $$\mathbb{P}(Z_n - Z_0 \geq \lambda) \leq \exp\!\left(\frac{-\lambda^2}{2(c_1^2 + \cdots + c_n^2)}\right).$$

## Depends on

- [Definition 9.2.1](126-definition-9-2-1.md)

## Proof depends on

- [Theorem 9.2.9 (Azuma's inequality for Doob martingales)](129-azuma-s-inequality-for-doob-martingales.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.2](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
