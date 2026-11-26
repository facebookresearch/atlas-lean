# Tight O(1/sqrt(T)) last-iterate convergence of extragradient and optimistic gradient

Let $F$ be monotone and $L$-Lipschitz on a compact convex set $\mathcal{Z}$ of diameter $D$. For the extragradient method and for optimistic gradient descent-ascent with constant step size $\eta \le c/L$ (for an absolute constant $c > 0$), the last iterate satisfies

$$
\mathrm{Gap}(z_T) = O\!\left(\frac{D \cdot \lVert z_1 - z^\star \rVert}{\eta \sqrt{T}}\right).
$$

In particular, when all players of a smooth monotone game with arbitrary compact convex action sets run either method, the last iterate is an $O(1/\sqrt T)$-approximate Nash equilibrium, matching the lower bound for this class of methods.

## Proof sketch

By the summability bound, some iterate among the first $T$ has $\lVert z_{t+1/2} - z_t\rVert = O(1/\sqrt T)$, which bounds its tangent residual by $O(1/(\eta \sqrt T))$. Monotonicity of the tangent residual transfers this to the last iterate, and $\mathrm{Gap} \le D \cdot r^{\tan}$ converts it into a gap bound. The optimistic method is handled by an analogous potential, and tightness follows from the lower bound for stationary canonical linear methods.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Proof depends on

- [Monotonicity of the tangent residual along extragradient iterates](tangent-residual-monotone-extragradient.md)
- [Last iterates of p-SCLI methods converge no faster than 1/sqrt(T)](last-iterate-lower-bound-sqrt-t.md)

## Sources

- Y. Cai, A. Oikonomou, W. Zheng, "Tight Last-Iterate Convergence of the Extragradient and the Optimistic Gradient Descent-Ascent Algorithm for Constrained Monotone Variational Inequalities", arXiv:2204.09228 (2022).
- Y. Cai, A. Oikonomou, W. Zheng, "Finite-Time Last-Iterate Convergence for Learning in Multi-Player Games", NeurIPS 2022.
