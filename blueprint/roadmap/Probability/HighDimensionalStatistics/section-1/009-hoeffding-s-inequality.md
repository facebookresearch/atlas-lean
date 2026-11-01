---
article_id: af_698138f870b7a391a4fce710
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: theorem_1_9_sample_mean
---

# Theorem 1.9 (Hoeffding's inequality)

Let $X_1, \ldots, X_n$ be $n$ independent random variables such that almost surely, $X_i \in [a_i, b_i]$ for all $i$. Let $\bar{X} = \frac{1}{n} \sum_{i=1}^{n} X_i$, then for any $t > 0$, $$\mathbb{P}(\bar{X} - \mathbb{E}(\bar{X}) > t) \leq \exp\left(-\frac{2n^2 t^2}{\sum_{i=1}^n (b_i - a_i)^2}\right),$$ and $$\mathbb{P}(\bar{X} - \mathbb{E}(\bar{X}) < -t) \leq \exp\left(-\frac{2n^2 t^2}{\sum_{i=1}^n (b_i - a_i)^2}\right).$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lemma 1.8 (Hoeffding's lemma (1963))](008-1963.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 1.2](../../../../sources/v1/HighDimensionalStatistics.md)
