---
article_id: af_e53a235f65be7d678c743d65
declaration: theorem
origin: cited
lean: TalagrandWeightedCertificates.talagrand_weighted_certificates
---

# Theorem 9.5.14 (Talagrand's inequality — functions with weighted certificates)

Let $\Omega = \Omega_1 \times \cdots \times \Omega_n$ equipped with the product measure. Let $f \colon \Omega \to \mathbb{R}$ be a function. Suppose for every $x \in \Omega$, there is some $\alpha(x) = (\alpha_1(x), \ldots, \alpha_n(x)) \in \mathbb{R}^n_{\geq 0}$ such that $f(y) \geq f(x) - \sum_{i \colon x_i \neq y_i} \alpha_i(x)$ for all $y \in \Omega$. Then, for every $t \geq 0$, $\mathbb{P}(|f - Mf| \geq t) \leq 4e^{-t^2/K^2}$ where $K = 2 \sup_{x \in \Omega} |\alpha(x)|$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 9.5.11 (Talagrand's inequality: general form)](155-talagrand-s-inequality-general-form.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.5](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
