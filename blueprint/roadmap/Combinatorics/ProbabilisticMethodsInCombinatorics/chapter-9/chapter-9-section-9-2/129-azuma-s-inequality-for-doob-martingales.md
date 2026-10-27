---
article_id: af_efab1691036dfa7bc1738e00
declaration: theorem
origin: cited
lean: Martingales.azuma_doob_martingale
---

# Theorem 9.2.9 (Azuma's inequality for Doob martingales)

Consider a Doob martingale $Z_i = \mathbb{E}[f(X_1, \ldots, X_n) \mid X_1, \ldots, X_i]$ as in Example 9.2.4. Suppose, conditioned on any value of $(X_1, \ldots, X_{i-1})$, the possibilities for $Z_i$ lie in an interval of length $c_i$ (here $c_i$ is non-random, but the location of the interval may depend on $X_1, \ldots, X_{i-1}$). Then for any $\lambda > 0$, $\mathbb{P}(Z_n - Z_0 \geq \lambda) \leq \exp\!\left(\frac{-2\lambda^2}{c_1^2 + \cdots + c_n^2}\right)$.

## Depends on

- [Definition 9.2.1](126-definition-9-2-1.md)

## Proof depends on

- [Theorem 3.3.1 (Markov's inequality)](../../chapter-3/033-markov-s-inequality.md)
- [Lemma 9.2.12 (Hoeffding's lemma)](130-hoeffding-s-lemma.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.2](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
