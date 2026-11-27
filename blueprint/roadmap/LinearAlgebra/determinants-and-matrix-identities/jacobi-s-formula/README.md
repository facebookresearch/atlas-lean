# Jacobi's formula

Let $A$ be a curve $\mathbb{R} \to \mathbb{R}^{n \times n}$ of real square matrices indexed by a finite set, differentiable at $t \in \mathbb{R}$. Then the derivative of $s \mapsto \det A(s)$ at $t$ is $\operatorname{tr}(\operatorname{adj}(A(t))\, A'(t))$, where $A'(t)$ is the derivative of $A$ at $t$ and $\operatorname{adj}$ is the adjugate matrix.

## Idea

The determinant is linear in each row, so by the product rule its derivative is the sum over $i$ of the determinants with the $i$-th row differentiated. Expanding each along that row and collecting the cofactors gives $\operatorname{tr}(\operatorname{adj}(A)\,A')$. When $A(t)$ is invertible, $\operatorname{adj}(A(t)) = \det A(t)\, A(t)^{-1}$, so the derivative is $\det A(t) \cdot \operatorname{tr}(A(t)^{-1} A'(t))$; dividing by $\det A(t)$, the derivative of $\log\lvert\det A\rvert$ at $t$ is $\operatorname{tr}(A(t)^{-1} A'(t))$. The formula is used in the Liouville formula for linear differential equations, in mechanics and in statistics, where it differentiates log-likelihoods of Gaussian models.

## Statements

- [Jacobi's formula](jacobi-det-derivative.md)
