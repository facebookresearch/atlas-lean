---
article_id: af_56160ec11cebc7d1b53dbff9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: LipschitzFunctions.concentration_equivalence
---

# Theorem 9.4.8 (Equivalence between notions of concentration of measure)

Let $t, \varepsilon \geq 0$. In a probability space $(\Omega, \mathbb{P})$ equipped with a metric. The following are equivalent: (a) (Expansion/approximate isoperimetry) If $A \subseteq \Omega$ with $\mathbb{P}(A) \geq 1/2$, then $\mathbb{P}(A_t) \geq 1 - \varepsilon$. (b) (Concentration of Lipschitz functions) If $f \colon \Omega \to \mathbb{R}$ is $1$-Lipschitz and $m \in \mathbb{R}$ satisfies $\mathbb{P}(f \leq m) \geq 1/2$, then $\mathbb{P}(f > m + t) \leq \varepsilon$.

## Depends on

- [Definition 9.4.7 (Lipschitz functions)](138-lipschitz-functions.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.4](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
