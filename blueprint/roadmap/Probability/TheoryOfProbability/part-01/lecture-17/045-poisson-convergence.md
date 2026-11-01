---
article_id: af_6e2aad24afdd58098ebffa8d
declaration: theorem
origin: cited
statement: formalized
lean: ProbabilityTheory.poisson_convergence
---

# Theorem (Poisson convergence)

Let $X_{n,m}$ be independent $\{0,1\}$-valued random variables with $P(X_{n,m} = 1) = p_{n,m}$. Suppose $\sum_{m=1}^{n} p_{n,m} \to \lambda$ and $\max_{1 \leq m \leq n} p_{n,m} \to 0$. Then $S_n = X_{n,1} + \cdots + X_{n,n} \Longrightarrow Z$ where $Z$ is $\operatorname{Poisson}(\lambda)$.

## Depends on

- [Definition (weak convergence)](../lecture-12/031-weak-convergence.md)
- [Definition (Poisson random variable)](047-poisson-random-variable.md)

## Proof depends on

- [Definition (characteristic function)](../lecture-8/019-characteristic-function.md)
- [Lévy's continuity theorem](../lecture-8/020-l-vy-s-continuity-theorem.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 17, Poisson convergence](../../../../../sources/v1/TheoryOfProbability.md)
