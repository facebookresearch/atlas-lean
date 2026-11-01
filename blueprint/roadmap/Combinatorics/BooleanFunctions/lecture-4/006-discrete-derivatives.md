---
article_id: af_b1ce79d91ed5a63e37a5c48e
declaration: def
origin: cited
statement: formalized
lean: BooleanFourier.discreteDerivative
---

# Definition 2.1 (Discrete derivatives)

Given a function $f \colon \{-1,1\}^n \to \mathbb{R}$ and $i \in [n]$, the discrete derivative of $f$ along $i$ is a function $\partial_i f \colon \{-1,1\}^{n-1} \to \mathbb{R}$ defined as $\partial_i f(y) = \frac{1}{2} (f(x_i = 1, x_{-i} = y) - f(x_i = -1, x_{-i} = y))$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.218 Analysis of Boolean Functions (Spring 2021), Lecture 4, Section 2](../../../../sources/v1/BooleanFunctions.md)
