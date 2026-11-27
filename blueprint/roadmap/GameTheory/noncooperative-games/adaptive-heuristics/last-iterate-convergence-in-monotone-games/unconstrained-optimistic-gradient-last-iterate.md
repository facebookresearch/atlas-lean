# Last-iterate convergence of optimistic gradient in unconstrained smooth monotone games

In an unconstrained ($\mathcal{Z} = \mathbb{R}^d$) monotone game whose operator $F$ is $L$-Lipschitz and has a $\Lambda$-Lipschitz Jacobian, with a zero $z^\star$ of $F$ within distance $D$ of both initial points, if all players run optimistic gradient descent with a constant step size $\eta \le \min\{1/(150 L), 1/(1711 D \Lambda)\}$, then $\lVert F(z_T) \rVert \le 60 D / (\eta \sqrt T)$. Hence the last iterate is an $O(1/\sqrt T)$-approximate Nash equilibrium in terms of the total gradient norm and of the total gap function over balls of radius $3D$ around the initial points ($O(m D^2/(\eta \sqrt T))$ for $m$ players); this rate is tight for optimistic gradient.

## Proof sketch

Some iterate among the first $T$ already has $\lVert F(z_t) \rVert = O(1/\sqrt T)$ (best-iterate convergence). From that time on, track an adaptively chosen potential built from the current and previous operator values and show, using monotonicity and the Lipschitz Jacobian, that it grows by at most a constant factor overall, so the last iterate stays within a constant factor of the best one. The lower bound follows from the $p$-SCLI lower bound, since optimistic gradient is a $2$-SCLI.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)
- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)

## Proof depends on

- [Last iterates of p-SCLI methods converge no faster than 1/sqrt(T)](last-iterate-lower-bound-sqrt-t.md)

## Sources

- N. Golowich, S. Pattathil, C. Daskalakis, "Tight last-iterate convergence rates for no-regret learning in multi-player games", NeurIPS 2020, arXiv:2010.13724, Theorem 5, Corollary 6 and Theorem 7.
