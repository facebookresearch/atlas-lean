# Anchoring accelerates last-iterate convergence to O(1/T)

For an $L$-Lipschitz monotone operator $F$ on $\mathbb{R}^d$ with a zero $z^\star$, the extra anchored gradient method

$$
z_{t+1/2} = z_t + \tfrac{1}{t+2}(z_0 - z_t) - \eta F(z_t), \qquad z_{t+1} = z_t + \tfrac{1}{t+2}(z_0 - z_t) - \eta F(z_{t+1/2}),
$$

with constant step size $\eta \in (0, 1/(8L)]$, satisfies $\lVert F(z_T) \rVert^2 = O\bigl(L^2 \lVert z_0 - z^\star \rVert^2 / T^2\bigr)$ (with $\eta = 1/(8L)$, $\lVert F(z_T) \rVert^2 \le 260 L^2 \lVert z_0 - z^\star \rVert^2 / (T + 1)^2$), i.e. the last iterate converges at rate $O(1/T)$ in operator norm, which is optimal, already for smooth convex-concave minimax problems, among deterministic first-order methods whose iterates lie in the span of the observed gradients; thus anchoring beats the $\Omega(1/\sqrt T)$ barrier of non-anchored extragradient and optimistic methods.

## Proof sketch

Construct a Lyapunov function of the form $a_t \lVert F(z_t)\rVert^2 + b_t \langle F(z_t), z_t - z_0\rangle$ with coefficients $a_t \sim t^2$ and $b_t \sim t$, and verify that it is non-increasing using monotonicity and Lipschitzness via a quadratic inequality. The analysis uses only monotonicity and Lipschitzness of $F$, so it applies to operators and not just to saddle gradients. A matching $\Omega(L^2 D^2 / T^2)$ lower bound follows from a worst-case bilinear (Krylov-subspace) construction.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Sources

- T. Yoon, E. K. Ryu, "Accelerated Algorithms for Smooth Convex-Concave Minimax Problems with O(1/k^2) Rate on Squared Gradient Norm", ICML 2021, arXiv:2102.07922, Theorem 1, Corollary 1, Section 2.3 and Theorem 3.
