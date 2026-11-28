# Averaged extragradient iterates converge at rate O(1/T)

Let $F$ be monotone and $L$-Lipschitz (with respect to the Euclidean norm) on a compact convex set $\mathcal{Z}$ of Euclidean diameter $D$. For the extragradient (mirror-prox) method with Euclidean projections and step size $\eta = 1/(\sqrt2\,L)$, started at $z_1 \in \mathcal{Z}$, with $z_{t+1/2} = \Pi_{\mathcal{Z}}(z_t - \eta F(z_t))$ and $z_{t+1} = \Pi_{\mathcal{Z}}(z_t - \eta F(z_{t+1/2}))$, the averaged midpoint $\bar z_T = \frac1T \sum_{t=1}^T z_{t + 1/2}$ satisfies the weak gap bound

$$
\max_{z \in \mathcal{Z}} \langle F(z), \bar z_T - z \rangle \le \frac{\sqrt2\, L D^2}{2T}.
$$

For a convex-concave saddle point problem $\min_{x \in X} \max_{y \in Y} f(x, y)$ with $\mathcal{Z} = X \times Y$ and $F(x, y) = (\nabla_x f(x, y), -\nabla_y f(x, y))$, the same bound holds for the duality gap $\max_{y \in Y} f(\bar x_T, y) - \min_{x \in X} f(x, \bar y_T)$ of $\bar z_T = (\bar x_T, \bar y_T)$.

## Proof sketch

The three-point inequality for the two projections gives, for every $z$, $\eta \langle F(z_{t+1/2}), z_{t+1/2} - z\rangle \le \tfrac12 \lVert z_t - z\rVert^2 - \tfrac12 \lVert z_{t+1} - z\rVert^2$, since $\eta L < 1$. Summing over $t$ telescopes to at most $\tfrac12\lVert z_1 - z\rVert^2 \le D^2/2$, and monotonicity replaces $F(z_{t+1/2})$ by $F(z)$; linearity in $z_{t+1/2}$ then passes to the average, and dividing by $\eta T$ gives $D^2/(2\eta T) = \sqrt2\, L D^2/(2T)$. For saddle point problems, convexity of $f(\cdot, y)$ and concavity of $f(x, \cdot)$ bound the duality gap of the average by the same averaged sum.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Sources

- A. Nemirovski, "Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems", SIAM Journal on Optimization 15(1) (2004), Theorem 3.2, bounds (3.9) and (3.10), and the Euclidean setup (5.1)–(5.2) in Section 5.
