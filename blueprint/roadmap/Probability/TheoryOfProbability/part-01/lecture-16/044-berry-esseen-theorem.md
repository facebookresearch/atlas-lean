---
article_id: af_af58d1d549b159f078be95fb
declaration: theorem
origin: cited
statement: formalized
lean: berry_esseen
---

# Theorem (Berry-Esseen theorem)

If $X_i$ are i.i.d. with mean zero, variance $\sigma^2$, and $E|X_i|^3 = \rho < \infty$, and $F_n(x)$ is the distribution of $(X_1 + \cdots + X_n) / (\sigma \sqrt{n})$ and $\Phi(x)$ is the standard normal distribution, then $|F_n(x) - \Phi(x)| \leq \frac{3\rho}{\sigma^3 \sqrt{n}}$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Fubini's theorem](../lecture-7/015-fubini-s-theorem.md)
- [Definition (characteristic function)](../lecture-8/019-characteristic-function.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 16, Berry-Esseen theorem](../../../../../sources/v1/TheoryOfProbability.md)
