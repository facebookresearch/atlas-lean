# Interior first-order conditions for profit maximization and cost minimization

Let $f : \mathbb R^n_{++} \to \mathbb R$ be a production function, $p$ the output price, and $w$ the vector of input prices. Let $x^*$ be a strictly positive input bundle at which $f$ is differentiable. Write $\partial_i f(x^*) = Df(x^*)e_i$, where $e_i$ is the $i$th coordinate vector.

1. **Profit.** If $x^*$ maximizes the profit $p f(x) - w \cdot x$ over $\mathbb R^n_{++}$, then $p\, \partial_i f(x^*) = w_i$ for every input $i$. This implication needs no sign assumption on prices.
2. **Cost.** If there is at least one input, all $w_i$ are positive, and $x^*$ minimizes $w \cdot x$ over strictly positive bundles with $f(x) \ge q$, with $f(x^*) = q$ and $Df(x^*) \ne 0$, then there is $\lambda > 0$ with $w_i = \lambda\, \partial_i f(x^*)$ for every $i$. In particular, every $\partial_j f(x^*)$ is positive, so both denominators are nonzero in the marginal-rate identity $\partial_i f(x^*) / \partial_j f(x^*) = w_i / w_j$, which holds for all $i,j$.

Profit stationarity does not by itself certify a maximum. With one input, $f(x) = x^2$ and $p = w = 1$, the condition $2x = 1$ holds at $x = 1/2$. This point minimizes the profit $x^2 - x$ on the positive half-line, is not a maximizer, and profit is unbounded above there.

When profit is concave on $\mathbb R^n_{++}$, an interior point satisfying the profit first-order conditions is a global maximizer. Profit is concave when $p \ge 0$ and $f$ is concave, as for a Cobb–Douglas technology $f(x) = \prod_i x_i^{a_i}$ with $a_i > 0$ and $\sum_i a_i < 1$.

## Background

- [Profit function of a production set](profit-fn.md)
- [Cost function](../cost-function/cost-fn.md)

## Sources

- A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University Press, 1995, Section 5.C (profit maximization and cost minimization)
