# Directional Cramér–Rao inequality

Under the hypotheses of the [Cramér–Rao inequality for a real estimand of a vector parameter](cramer-rao-multiparameter.md), except that the Fisher information matrix $I(\theta)$ need not be positive definite, for every direction $a \in \mathbb R^k$,

$$\langle a, \nabla g(\theta)\rangle^2 \le \bigl(a^{\mathsf T} I(\theta) \, a\bigr) \operatorname{Var}_\theta T, \qquad I(\theta)_{ij} = \int \frac{\partial_i p_\theta \, \partial_j p_\theta}{p_\theta} \, d\nu .$$

It is the one-parameter inequality for the subfamily $t \mapsto p_{\theta + t a}$. Along that line the score is $\sum_i a_i \partial_i p_\theta / p_\theta$ (the gradient of $p_\cdot(x)$ vanishes where $p_\theta(x) = 0$, a minimum of a nonnegative function), its Fisher information is the quadratic form $a^{\mathsf T} I(\theta) a$, the derivative of the estimand is $\langle a, \nabla g(\theta)\rangle$, and the integrability hypotheses along the line follow from those of the coordinates by the inequalities $2|uv| \le u^2 + v^2$.

## Informally uses

- [Cramér–Rao inequality, multiplicative form](sq-deriv-le-fisher-information-mul.md): the one-parameter inequality, applied to the line $t \mapsto \theta + t a$.

## Sources

- C. R. Rao, "Information and the accuracy attainable in the estimation of statistical parameters", *Bull. Calcutta Math. Soc.* 37 (1945) 81–91.
