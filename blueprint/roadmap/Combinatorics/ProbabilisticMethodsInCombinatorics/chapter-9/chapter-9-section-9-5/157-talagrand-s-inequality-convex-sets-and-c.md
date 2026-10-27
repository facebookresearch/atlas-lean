---
article_id: af_c1e622a1e4923d10eb94cca8
declaration: theorem
origin: cited
statement: formalized
lean: Talagrand.talagrand_convex_lipschitz_combined
---

# Corollary 9.5.13 (Talagrand's inequality: convex sets and convex Lipschitz functions)

Let $x = (x_1, \ldots, x_n) \in [0,1]^n$ be independent random variables (not necessarily identical). Let $t \geq 0$. Let $A \subseteq [0,1]^n$ be a convex set. Then $\mathbb{P}(x \in A) \cdot \mathbb{P}(\operatorname{dist}(x, A) \geq t) \leq e^{-t^2/4}$ where $\operatorname{dist}$ is Euclidean distance. Also, if $f \colon [0,1]^n \to \mathbb{R}$ is a convex $1$-Lipschitz function, then $\mathbb{P}(|f - Mf| \geq t) \leq 4e^{-t^2/4}$.

## Depends on

- [Definition 9.4.7 (Lipschitz functions)](../chapter-9-section-9-4/138-lipschitz-functions.md)

## Proof depends on

- [Theorem 9.5.11 (Talagrand's inequality: general form)](155-talagrand-s-inequality-general-form.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.5](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
