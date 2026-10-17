---
article_id: af_a777c5e41f8f635edb7694d2
declaration: theorem
origin: cited
statement: formalized
lean: ProbabilityTheory.lindeberg_feller_clt_triangular
---

# Theorem (Lindeberg-Feller theorem)

Suppose $X_{n,m}$ are independent expectation-zero random variables when $1 \leq m \leq n$ (triangular array). Suppose $\sum_{m=1}^{n} E[X_{n,m}^2] \to \sigma^2 > 0$ and for all $\epsilon$, $\lim_{n \to \infty} E(|X_{n,m}|^2;\, |X_{n,m}| > \epsilon) = 0$. Then $S_n = X_{n,1} + X_{n,2} + \cdots + X_{n,n} \Longrightarrow \sigma \chi$ (where $\chi$ is standard normal) as $n \to \infty$.

## Depends on

- [Definition (weak convergence)](../lecture-12/031-weak-convergence.md)

## Proof depends on

- [Definition (characteristic function)](../lecture-8/019-characteristic-function.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 16, Lindeberg-Feller theorem](../../../../../sources/v1/TheoryOfProbability.md)
