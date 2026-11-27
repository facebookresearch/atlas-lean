# Last iterates of p-SCLI methods converge no faster than 1/sqrt(T)

For smooth convex-concave saddle point problems (hence for smooth monotone variational inequalities), last iterates of stationary canonical linear iterative methods are slow on bilinear instances $f(x, y) = x^\top M y + b_1^\top x + b_2^\top y$ with $L$-Lipschitz operator. Because the primal-dual gap over all of $\mathbb{R}^n$ is infinite for such $f$, the gap is measured over balls of radius proportional to $D$.

- A *$1$-SCLI* produces, on an affine operator $F(z) = Az + b$, iterates $z^{(t)} = C_0(A) z^{(t-1)} + N(A) b$ for fixed maps $C_0, N$; it is consistent if its iterates converge to the solution $-A^{-1} b$ for every invertible $A$ of this form. Every consistent $1$-SCLI whose inversion matrix $N(A)$ is a polynomial of degree at most $k - 1$ in $A$, which includes the extragradient method with constant step size, started at $z^{(0)} = 0$, satisfies for every $T$: over the bilinear instances with full-rank $M$ and solution $z^\star = (x^\star, y^\star)$ at distance $D$ from $0$, the supremum of the primal-dual gap $\sup_{\lVert y' - y^\star \rVert \le D} f(x, y') - \inf_{\lVert x' - x^\star \rVert \le D} f(x', y)$ of its iterate $(x, y)$ after $T$ steps is at least $L D^2 / (k \sqrt{20 T})$; the instances nearly attaining it depend on $T$.
- A *$p$-SCLI* generates, from $p$ initialization points $z^{(0)}, \dots, z^{(-p+1)}$, iterates $z^{(t)} = \sum_{j=0}^{p-1} \bigl(\alpha_j F(z^{(t-p+j)}) + \beta_j z^{(t-p+j)}\bigr)$ for fixed real scalars $\alpha_j, \beta_j$; optimistic gradient descent-ascent with constant step size is a $2$-SCLI. Write $\mathcal{D}_R = B(0, R) \times B(0, R)$. For every $p$-SCLI there are constants $c_A, T_A > 0$ depending on the algorithm such that for every $T \ge T_A$ some bilinear instance with equilibrium in $\mathcal{D}_D$ and some initialization in $\mathcal{D}_D$ give, at some iteration $T' \in \{T, \dots, T + p - 1\}$, total gap at least $c_A L D^2 / \sqrt{T}$, where each player's improvement is measured over deviations in its ball of radius $2D$, i.e. with respect to $\mathcal{D}_{2D}$.

In contrast, the averaged extragradient iterate converges at rate $O(1/T)$.

## Proof sketch

Restrict to bilinear games $\min_x \max_y x^\top M y$, on which such methods act as fixed linear recursions whose coefficient matrices are polynomials in the operator matrix. The error after $T$ steps is then governed by the spectrum of these polynomials, and choosing the instance depending on $T$ (and on the algorithm) so that some eigencomponent has not yet been damped reduces the lower bound to an inequality about polynomials of bounded degree, which gives $\Omega(1/\sqrt T)$ for the gap of the last iterate.

## Depends on

- [Extragradient and optimistic gradient descent-ascent](extragradient-and-optimistic-gradient.md)
- [Gap function and tangent residual for monotone variational inequalities](gap-function-and-tangent-residual.md)
- [Smooth monotone game and monotone variational inequality](smooth-monotone-game-variational-inequality.md)
- [Averaged extragradient iterates converge at rate O(1/T)](mirror-prox-averaged-rate.md)

## Sources

- N. Golowich, S. Pattathil, C. Daskalakis, A. Ozdaglar, "Last Iterate is Slower than Averaged Iterate in Smooth Convex-Concave Saddle Point Problems", COLT 2020, arXiv:2002.00057, Definitions 4, 5 and 7 and Theorem 9 ($1$-SCLIs).
- N. Golowich, S. Pattathil, C. Daskalakis, "Tight last-iterate convergence rates for no-regret learning in multi-player games", NeurIPS 2020, arXiv:2010.13724, Definitions 3 and 5 and Theorem 7 ($p$-SCLIs).
