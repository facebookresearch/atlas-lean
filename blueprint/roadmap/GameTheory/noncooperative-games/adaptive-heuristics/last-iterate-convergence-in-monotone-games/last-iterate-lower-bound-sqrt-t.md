# Last iterates of p-SCLI methods converge no faster than 1/sqrt(T)

For smooth convex-concave saddle point problems (hence for smooth monotone variational inequalities), last iterates of $p$-stationary canonical linear iterative methods ($p$-SCLIs, whose update on an affine operator is a fixed linear recursion in the last $p$ iterates) are slow on bilinear instances with $L$-Lipschitz operator and solutions within distance $D$. Every consistent $1$-SCLI whose inversion matrix is a polynomial of degree less than $k$ in the operator matrix, which includes the extragradient method with constant step size, has last iterate with primal-dual gap at least $L D^2/(k \sqrt{20 T})$ after $T$ iterations on some bilinear instance (depending on $T$). For every $p$-SCLI, which includes optimistic gradient descent-ascent ($p = 2$) with constant step size, there are constants $c_A, T_A > 0$ depending on the algorithm such that for every $T \ge T_A$ some bilinear instance and initialization give gap at least $c_A L D^2 / \sqrt{T}$ at some iteration $T' \in \{T, \dots, T + p - 1\}$. In contrast, the averaged extragradient iterate converges at rate $O(1/T)$.

## Proof sketch

Restrict to bilinear games $\min_x \max_y x^\top M y$, on which such methods act as fixed linear recursions whose coefficient matrices are polynomials in the operator matrix. The error after $T$ steps is then governed by the spectrum of these polynomials, and choosing the instance depending on $T$ (and on the algorithm) so that some eigencomponent has not yet been damped reduces the lower bound to an inequality about polynomials of bounded degree, which gives $\Omega(1/\sqrt T)$ for the gap of the last iterate.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)

## Sources

- N. Golowich, S. Pattathil, C. Daskalakis, A. Ozdaglar, "Last Iterate is Slower than Averaged Iterate in Smooth Convex-Concave Saddle Point Problems", COLT 2020, arXiv:2002.00057, Theorem 9 ($1$-SCLIs).
- N. Golowich, S. Pattathil, C. Daskalakis, "Tight last-iterate convergence rates for no-regret learning in multi-player games", NeurIPS 2020, arXiv:2010.13724, Theorem 7 ($p$-SCLIs).
