---
article_id: af_0b26cffcfb3e71e8f8bf2fca
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: fubini_theorem
---

# Fubini's theorem

Consider $\sigma$-finite measure spaces $(X, \mathcal{A}, \mu_1)$ and $(Y, \mathcal{B}, \mu_2)$. Let $\Omega = X \times Y$ and $\mathcal{F}$ be the product $\sigma$-algebra. There is a unique measure $\mu$ on $\mathcal{F}$ with $\mu(A \times B) = \mu_1(A) \mu_2(B)$. If $f \geq 0$ or $\int |f| \, d\mu < \infty$ then $$\int_{X} \int_{Y} f(x,y) \, \mu_2(dy) \, \mu_1(dx) = \int_{X \times Y} f \, d\mu = \int_{Y} \int_{X} f(x,y) \, \mu_1(dx) \, \mu_2(dy).$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem (π-system and λ-system)](../lecture-2/002-system-and-system.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 7](../../../../../sources/v1/TheoryOfProbability.md)
