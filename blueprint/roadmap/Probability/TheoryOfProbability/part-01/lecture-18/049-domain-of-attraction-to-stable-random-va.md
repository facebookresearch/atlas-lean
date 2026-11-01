---
article_id: af_8ec821fd3891b6ca72c5e698
declaration: theorem
origin: cited
statement: formalized
lean: ProbabilityTheory.domain_of_attraction_of_tail_conditions
---

# Theorem (Domain of attraction to stable random variable)

Suppose that $\lim_{x \to \infty} P(X_1 > x) / P(|X_1| > x) = \theta \in [0,1]$ and $P(|X_1| > x) = x^{-\alpha} L(x)$ where $L$ is slowly varying (which means $\lim_{x \to \infty} L(tx) / L(x) = 1$ for all $t > 0$). Then $(S_n - b_n) / a_n$ converges in law to a limiting random variable, for appropriate $a_n$ and $b_n$ values.

## Depends on

- [Definition (weak convergence)](../lecture-12/031-weak-convergence.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 18, Domain of attraction to stable random variable](../../../../../sources/v1/TheoryOfProbability.md)
