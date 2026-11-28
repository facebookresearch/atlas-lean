# Tight O(1/sqrt(T)) last-iterate convergence of extragradient and optimistic gradient

Let $F$ be monotone and $L$-Lipschitz on a compact convex set $\mathcal{Z}$ of diameter $D$, with a solution $z^\star$ of the variational inequality. For the extragradient method with any constant step size $\eta \in (0, 1/L)$, started at $z_0$, the last iterate $z_T$ after $T \ge 1$ updates satisfies

$$
\mathrm{Gap}(z_T) \le \frac{3 D\, \lVert z_0 - z^\star \rVert}{\eta \sqrt{T} \sqrt{1 - \eta^2 L^2}},
$$

and the same bound holds for its tangent residual with $D$ omitted. For optimistic gradient descent-ascent with any constant step size $\eta \in (0, 1/(2L))$, started from an initial base point and an initial extrapolated point, whose operator value drives the first update, the base iterate after $T \ge 1$ updates (written $w_T$ in the definition of the method) satisfies $\mathrm{Gap}(w_T) \le D D_0 / \bigl(\eta \sqrt{T} \sqrt{1 - 4\eta^2 L^2}\bigr)$, where $D_0$ is of the order of the larger of the distance from the initial base point to $z^\star$ and the distance between the two initial points.

In particular, when all players of a smooth monotone game with arbitrary compact convex action sets run either method, the last iterate is an $O(1/\sqrt T)$-approximate Nash equilibrium, matching the lower bound for this class of methods.

## Proof sketch

By the summability bound, some iterate among the first $T$ has $\lVert z_{t+1/2} - z_t\rVert = O(1/\sqrt T)$, which bounds its tangent residual by $O(1/(\eta \sqrt T))$. Monotonicity of the tangent residual transfers this to the last iterate, and $\mathrm{Gap} \le D \cdot r^{\tan}$ converts it into a gap bound. The optimistic method is handled by the potential given by the squared tangent residual at the base point plus the squared difference of the operator values at the base and the extrapolated point, which is non-increasing for $\eta < 1/(2L)$, and tightness follows from the lower bound for stationary canonical linear methods.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Proof depends on

- [Monotonicity of the tangent residual along extragradient iterates](tangent-residual-monotone-extragradient.md)
- [Last iterates of p-SCLI methods converge no faster than 1/sqrt(T)](last-iterate-lower-bound-sqrt-t.md)

## Sources

- Y. Cai, A. Oikonomou, W. Zheng, "Finite-Time Last-Iterate Convergence for Learning in Multi-Player Games", NeurIPS 2022; full version "Tight Last-Iterate Convergence of the Extragradient and the Optimistic Gradient Descent-Ascent Algorithm for Constrained Monotone Variational Inequalities", arXiv:2204.09228.
