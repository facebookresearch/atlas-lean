---
article_id: af_04796239e0467325a055298a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: kolmogorov_zero_one_of_iIndepFun
---

# Theorem (Kolmogorov zero-one law)

Consider a sequence of random variables $X_n$ on some probability space. Write $\mathcal{F}'_n = \sigma(X_n, X_{n+1}, \ldots)$ and $\mathcal{T} = \bigcap_n \mathcal{F}'_n$. $\mathcal{T}$ is called the tail $\sigma$-algebra. If $X_1, X_2, \ldots$ are independent and $A \in \mathcal{T}$ then $P(A) \in \{0, 1\}$.

## Depends on

- [Definition (tail σ-algebra)](033-tail-algebra.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 10, Kolmogorov zero-one law](../../../../../sources/v1/TheoryOfProbability.md)
