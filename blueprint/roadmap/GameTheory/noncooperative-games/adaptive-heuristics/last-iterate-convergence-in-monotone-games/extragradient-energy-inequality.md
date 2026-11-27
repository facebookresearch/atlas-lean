# Energy inequality for the extragradient method

Let $F$ be monotone and $L$-Lipschitz on a closed convex set $\mathcal{Z}$ with a solution $z^\star$ of the variational inequality, and run the extragradient method with step size $\eta < 1/L$. Then for every $t$,

$$
\lVert z_{t+1} - z^\star \rVert^2 \le \lVert z_t - z^\star \rVert^2 - (1 - \eta^2 L^2)\, \lVert z_{t+1/2} - z_t \rVert^2 ,
$$

so the distances to every solution are nonincreasing and $\sum_{t} \lVert z_{t + 1/2} - z_t\rVert^2 \le \lVert z_1 - z^\star\rVert^2 / (1 - \eta^2 L^2)$.

## Proof sketch

The projection inequalities for $z_{t+1/2}$ and $z_{t+1}$ give $\lVert z_{t+1} - z^\star\rVert^2 \le \lVert z_t - z^\star\rVert^2 - \lVert z_{t+1} - z_{t+1/2}\rVert^2 - \lVert z_{t+1/2} - z_t\rVert^2 + 2\eta \langle F(z_t) - F(z_{t+1/2}), z_{t+1} - z_{t+1/2}\rangle - 2\eta \langle F(z_{t+1/2}), z_{t+1/2} - z^\star\rangle$. The last term is nonpositive by monotonicity and the variational inequality at $z^\star$; the cross term is at most $\eta^2 L^2 \lVert z_{t+1/2} - z_t\rVert^2 + \lVert z_{t+1} - z_{t+1/2}\rVert^2$ by Lipschitzness and Young's inequality.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Sources

- G. M. Korpelevich, "The extragradient method for finding saddle points and other problems", Ekonomika i Matematicheskie Metody 12 (1976).
- Y. Cai, A. Oikonomou, W. Zheng, "Finite-Time Last-Iterate Convergence for Learning in Multi-Player Games", NeurIPS 2022; full version "Tight Last-Iterate Convergence of the Extragradient and the Optimistic Gradient Descent-Ascent Algorithm for Constrained Monotone Variational Inequalities", arXiv:2204.09228.
