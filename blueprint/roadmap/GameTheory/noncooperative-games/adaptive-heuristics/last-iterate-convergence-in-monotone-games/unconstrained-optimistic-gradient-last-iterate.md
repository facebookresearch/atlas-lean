# Last-iterate convergence of optimistic gradient in unconstrained smooth monotone games

In an unconstrained ($\mathcal{Z} = \mathbb{R}^d$) $L$-smooth monotone game whose operator is additionally Lipschitz in its Jacobian, if all players run optimistic gradient descent with a suitable constant step size, then $\lVert F(z_T) \rVert = O(1/\sqrt T)$, so the last iterate is an $O(1/\sqrt T)$-approximate Nash equilibrium in terms of the total gradient norm and the gap restricted to bounded neighbourhoods; this rate is tight for optimistic gradient.

## Proof sketch

Track the potential $\lVert F(z_t)\rVert^2$ plus a correction involving the difference of consecutive operator values, and show it is non-increasing using monotonicity and the second-order smoothness assumption. Combined with the summability of squared operator norms along the trajectory, which follows from the standard energy inequality, this yields the $O(1/\sqrt T)$ rate; the lower bound follows from the linear-iterative-method lower bound.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Proof depends on

- [Last iterates of p-SCLI methods converge no faster than 1/sqrt(T)](last-iterate-lower-bound-sqrt-t.md)

## Sources

- N. Golowich, S. Pattathil, C. Daskalakis, "Tight last-iterate convergence rates for no-regret learning in multi-player games", NeurIPS 2020, arXiv:2010.13724.
