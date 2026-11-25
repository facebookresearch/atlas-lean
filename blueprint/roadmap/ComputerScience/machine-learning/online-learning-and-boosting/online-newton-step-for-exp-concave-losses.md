# Online Newton Step for exp-concave losses

Let $K \subseteq \mathbb{R}^n$ be compact and convex with diameter $D > 0$, and let the losses $f_t$ be $\alpha$-exp-concave on
$K$ with $\alpha > 0$ and gradients bounded by $G > 0$. Online Newton Step with
$\gamma = \tfrac12 \min\{1/(4GD), \alpha\}$, $\varepsilon = 1/(\gamma^2 D^2)$, $A_0 = \varepsilon I$,
$A_t = A_{t-1} + \nabla_t \nabla_t^{\mathsf T}$, $y_{t+1} = x_t - \gamma^{-1} A_t^{-1} \nabla_t$ and $x_{t+1}$ the
projection of $y_{t+1}$ onto $K$ in the norm induced by $A_t$, has regret at most $2(1/\alpha + GD)\, n \log T$ for $T \ge 4$
(Hazan, Theorem 4.5). The cases $G = 0$ or $D = 0$ are trivial (zero regret) and are excluded from the parameter
formulas.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Online convex optimization and projected OGD regret.

## Sources

- E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207, Section 4.4: Algorithm 12 (online Newton step) and Theorem 4.5. <https://arxiv.org/pdf/1909.05207>
