---
article_id: af_61ce5aefe04307ac0db6b146
declaration: theorem
origin: cited
statement: formalized
lean: SubGaussian.lemma_9_4_20
---

# Lemma 9.4.20 (Median vs. mean for subGaussian distributions)

There exists a constant $C > 0$ so that the following holds for any real random variable $X$ satisfying, for some constants $m$ and $K$, $\mathbb{P}(|X - m| \geq t) \leq 2e^{-t^2/K^2}$ for all $t \geq 0$. (a) Every median $MX$ of $X$ satisfies $|MX - m| \leq CK$. (b) The mean of $X$ satisfies $|\mathbb{E}X - m| \leq CK$. (c) For any $p \geq 1$, writing $\|X\|_p \coloneqq (\mathbb{E}|X|^p)^{1/p}$ for the $L^p$ norm of $X$, $|\|X\|_p - m| \leq CK\sqrt{p}$. (d) For every constant $A$ there exists a constant $c > 0$ so that if $|m' - m| \leq AK$, then $\mathbb{P}(|X - m'| \geq t) \leq 2e^{-ct^2/K^2}$ for all $t \geq 0$.

## Depends on

- [Definition 9.4.17 (Sub-Gaussian distribution)](146-sub-gaussian-distribution.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.4](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
