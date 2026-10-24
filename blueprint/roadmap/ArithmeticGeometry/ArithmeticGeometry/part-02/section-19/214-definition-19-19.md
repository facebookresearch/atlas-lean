---
article_id: af_b97699e5db07f96a5fe3b053
declaration: def
origin: cited
statement: formalized
lean: CurveMorphismData.pullback
---

# Definition 19.19

Let $\phi: C_1 \rightarrow C_2$ be a morphism defined over $k$. The pullback map $\phi^*$ on divisors is the homomorphism $\phi^*: \operatorname{Div}_k C_2 \rightarrow \operatorname{Div}_k C_1$ defined by $\phi^*(Q) \coloneqq \sum_{P \in \phi^{-1}(Q)} e_{\phi}(P) P$ where $(Q)$ denotes the divisor in $\operatorname{Div}_k C_2$ with support $\{Q\}$ and $n_Q = 1$. We also define the pushforward map $\phi_*$ on divisors as the homomorphism $\phi_*: \operatorname{Div} C_1 \rightarrow \operatorname{Div} C_2$ defined by $\phi_*(P) = [k(P): \phi^*(k(P))] \phi(P) = \frac{\operatorname{deg} P}{\operatorname{deg} \phi(P)} \phi(P)$.

## Depends on

- [Definition 19.6](203-definition-19-6.md)
- [Definition 19.9](206-definition-19-9.md)
- [Definition 19.18](213-definition-19-18.md)

## Sources

- [MIT 18.782 Introduction to Arithmetic Geometry (Fall 2013), Section 19.2](../../../../../sources/v1/ArithmeticGeometry.md)
