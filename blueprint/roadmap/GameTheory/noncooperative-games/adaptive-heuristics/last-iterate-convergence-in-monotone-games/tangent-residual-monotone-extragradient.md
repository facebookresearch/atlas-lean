# Monotonicity of the tangent residual along extragradient iterates

Let $F$ be monotone and $L$-Lipschitz on a compact convex set $\mathcal{Z}$, and run the extragradient method with step size $\eta \in (0, 1/L)$. Then the tangent residual of the iterates is non-increasing, $r^{\tan}(z_{t+1}) \le r^{\tan}(z_t)$ for every $t$, and $\sum_{t \le T} \lVert z_{t+1/2} - z_t \rVert^2 \le \lVert z_1 - z^\star \rVert^2 /(1 - \eta^2 L^2)$ for any solution $z^\star$.

## Proof sketch

The summability bound follows from the standard extragradient energy inequality $\lVert z_{t+1} - z^\star\rVert^2 \le \lVert z_t - z^\star\rVert^2 - (1 - \eta^2 L^2)\lVert z_{t+1/2} - z_t\rVert^2$. Monotonicity of the residual requires a potential argument certified by a sum-of-squares decomposition: a quadratic form in the iterates, gradients and normal-cone elements that is nonnegative under monotonicity, Lipschitzness and the projection optimality conditions, which implies that the tangent residual cannot increase.

## Depends on

- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)
- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Proof depends on

- [Energy inequality for the extragradient method](extragradient-energy-inequality.md)

## Sources

- Y. Cai, A. Oikonomou, W. Zheng, "Finite-Time Last-Iterate Convergence for Learning in Multi-Player Games", NeurIPS 2022; full version "Tight Last-Iterate Convergence of the Extragradient and the Optimistic Gradient Descent-Ascent Algorithm for Constrained Monotone Variational Inequalities", arXiv:2204.09228.
