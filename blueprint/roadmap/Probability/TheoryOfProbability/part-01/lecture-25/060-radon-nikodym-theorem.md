---
article_id: af_35c1774e47ea34f2cb876766
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: radon_nikodym_setLIntegral'
---

# Theorem (Radon-Nikodym theorem)

If $\mu$ and $\nu$ are $\sigma$-finite measures on $(\Omega, \mathcal{F})$ and $\nu$ is absolutely continuous w.r.t. $\mu$ (i.e., $\mu(A) = 0$ implies $\nu(A) = 0$), then there exists a measurable $f \colon \Omega \to [0, \infty)$ such that $\nu(A) = \int_A f \, d\mu$.

## Depends on

- [Definition (Absolutely continuous)](054-absolutely-continuous.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 25, Conditional expectation section](../../../../../sources/v1/TheoryOfProbability.md)
