# Averaged extragradient iterates converge at rate O(1/T)

Let $F$ be monotone and $L$-Lipschitz on a compact convex set $\mathcal{Z}$ of diameter $D$. For the extragradient (mirror-prox) method with Euclidean projections and step size $\eta \in (0, 1/L]$, the averaged midpoint $\bar z_T = \frac1T \sum_{t=1}^T z_{t + 1/2}$ satisfies the weak gap bound

$$
\max_{z \in \mathcal{Z}} \langle F(z), \bar z_T - z \rangle \le \frac{D^2}{2 \eta T},
$$

which is $L D^2 / (2T)$ for $\eta = 1/L$; for convex-concave saddle point problems the same argument bounds the duality gap of $\bar z_T$ by $O(L D^2 / T)$.

## Proof sketch

The three-point inequality for the two projections gives, for every $z$, $\eta \langle F(z_{t+1/2}), z_{t+1/2} - z\rangle \le \tfrac12 \lVert z_t - z\rVert^2 - \tfrac12 \lVert z_{t+1} - z\rVert^2$ when $\eta L \le 1$. Summing over $t$ telescopes, and monotonicity replaces $F(z_{t+1/2})$ by $F(z)$; convexity in $z_{t+1/2}$ of the linear function then passes to the average.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Sources

- A. Nemirovski, "Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems", SIAM Journal on Optimization 15(1) (2004).
