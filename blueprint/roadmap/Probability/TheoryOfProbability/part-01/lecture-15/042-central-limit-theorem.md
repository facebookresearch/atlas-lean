---
article_id: af_4c9a06d61cf8eb3bd91d270a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: central_limit_theorem
---

# Theorem (Central Limit Theorem)

Let $X_1, X_2, \ldots$ be i.i.d. with $E[X_i] = \mu$, $\operatorname{Var}(X_i) = \sigma^2 \in (0, \infty)$. If $S_n = X_1 + \cdots + X_n$ then $(S_n - n\mu) / (\sigma \sqrt{n})$ converges in law to a standard normal.

## Depends on

- [Definition (weak convergence)](../lecture-12/031-weak-convergence.md)

## Proof depends on

- [Definition (characteristic function)](../lecture-8/019-characteristic-function.md)
- [Lévy's continuity theorem](../lecture-8/020-l-vy-s-continuity-theorem.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 15, Moments, derivatives, CLT](../../../../../sources/v1/TheoryOfProbability.md)
