---
article_id: af_9afbadf2f7c8f717c52e6044
declaration: def
origin: cited
statement: formalized
lean: ConditionalExpectation.condExp
---

# Definition (Conditional expectation)

Given a probability space $(\Omega, \mathcal{F}_0, P)$ and a $\sigma$-field $\mathcal{F} \subset \mathcal{F}_0$ and a random variable $X$ measurable w.r.t. $\mathcal{F}_0$, with $E|X| < \infty$, the conditional expectation of $X$ given $\mathcal{F}$ is a random variable $Y = E(X \mid \mathcal{F})$ such that $Y$ is $\mathcal{F}$-measurable and for all $A \in \mathcal{F}$, $\int_A X \, dP = \int_A Y \, dP$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 25, Conditional expectation](../../../../../sources/v1/TheoryOfProbability.md)
