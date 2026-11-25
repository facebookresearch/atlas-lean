# Interior first-order conditions for profit maximization and cost minimization

Let $f : \mathbb R^n_{++} \to \mathbb R$ be a continuously differentiable production function, $p > 0$ the output price and $w \in \mathbb R^n_{++}$ the input prices.

1. **Profit.** If $x^* \in \mathbb R^n_{++}$ maximizes the profit $p f(x) - w \cdot x$ over $\mathbb R^n_{++}$, then $p\, \partial_i f(x^*) = w_i$ for every input $i$.
2. **Cost.** If $x^* \in \mathbb R^n_{++}$ minimizes $w \cdot x$ subject to $f(x) \ge q$, with $f(x^*) = q$ and $\nabla f(x^*) \ne 0$, then there is $\lambda > 0$ with $w_i = \lambda\, \partial_i f(x^*)$ for every $i$; hence the marginal rate of technical substitution equals the price ratio, $\partial_i f(x^*) / \partial_j f(x^*) = w_i / w_j$.

These conditions are necessary, not sufficient. For the convex technology $f(x) = x^2$ with one input and $p = w = 1$, the condition $2x = 1$ holds at $x = 1/2$, which minimizes the profit $x^2 - x$ locally, and profit is unbounded above. When $f$ is concave, for example a Cobb–Douglas technology $f(x) = \prod_i x_i^{a_i}$ with $a_i > 0$ and $\sum_i a_i < 1$, the profit is concave and an interior point satisfying the first-order conditions is a global maximizer.

## Proof depends on

- [Karush–Kuhn–Tucker conditions for inequality constraints](../../../Analysis/convex-analysis-and-variations/karush-kuhn-tucker-inequality.md)

## Background

- [Profit function of a production set](profit-fn.md)
- [Cost function](../cost-function/cost-fn.md)

## Sources

- A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University Press, 1995, Section 5.C (profit maximization and cost minimization)
