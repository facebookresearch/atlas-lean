# Regularized Follow-the-Leader / Online Mirror Descent regret

This node collects regret bounds for regularized follow-the-leader and online mirror descent with linear
losses on a convex set $K$.

## Expansion

A sound expansion has separate pages for:

1. **RFTL regret.** If $K$ is bounded, closed and convex, $R$ is strongly convex, smooth and twice differentiable,
   $x_1 = \arg\min_{x \in K} R(x)$ and $x_{t+1} = \arg\min_{x \in K} \eta \sum_{s \le t} \langle g_s, x \rangle + R(x)$, then for
   every $u \in K$ the regret is at most $2\eta \sum_t (\lVert g_t \rVert_t^*)^2 + \frac{R(u) - R(x_1)}{\eta}$, where
   $\lVert \cdot \rVert_t^*$ is the dual of the local norm given by the Hessian of $R$ at a point between $x_t$ and $x_{t+1}$.
2. **Equivalence.** For linear losses, lazy online mirror descent with regularizer $R$ and Bregman projections
   onto $K$ produces the same iterates as RFTL with the same $R$ and $\eta$.
3. **Exponentiated gradient.** The negative-entropy regularizer on the simplex gives the exponentiated-gradient
   (Hedge) update, with regret at most $2G_\infty\sqrt{2T\log n}$ for gradients of sup-norm at most $G_\infty$.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Online convex optimization and projected OGD regret.

## Sources

- E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207, Section 5.2: Algorithm 13 and Theorem 5.2 (RFTL regret in local norms); Section 5.3: the lazy and agile mirror-descent forms, their equivalence with RFTL for linear losses, Theorem 5.6, and Corollary 5.7 (exponentiated gradient). <https://arxiv.org/pdf/1909.05207>
