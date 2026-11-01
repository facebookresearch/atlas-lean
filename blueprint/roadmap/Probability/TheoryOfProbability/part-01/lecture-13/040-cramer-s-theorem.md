---
article_id: af_8d56b3a4877b7246ba35197d
declaration: theorem
origin: cited
lean: cramer_theorem
---

# Theorem (Cramer's theorem)

Let $\mu_n$ be the law of the empirical mean $A_n = \frac{1}{n} \sum_{j=1}^n X_j$ for i.i.d. vectors $X_1, X_2, \dots, X_n$ in $\mathbb{R}^d$ with the same law as $X$. Define $\Lambda(\lambda) = \log \mathbb{E}[e^{\langle \lambda, X \rangle}]$ and $\Lambda^*(x) = \sup_{\lambda \in \mathbb{R}^d} \{\langle \lambda, x \rangle - \Lambda(\lambda)\}$. Then $\mu_n$ satisfy the LDP with convex rate function $\Lambda^*$.

## Depends on

- [Definition (rate function and large deviation principle)](039-rate-function-and-large-deviation-princi.md)
- [Definition (moment generating function)](../lecture-8/016-moment-generating-function.md)

## Proof depends on

- [Definition (Legendre transform)](029-legendre-transform.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 13, Cramer's theorem section](../../../../../sources/v1/TheoryOfProbability.md)
