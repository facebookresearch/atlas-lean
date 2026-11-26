# Sparse regression for learning reaction–diffusion equations

Let $u(x, t) \ge 0$ be a population density observed with noise on a grid $\{(x_i, t_j)\}$, and let $\hat u$ be a smooth surrogate of $u$ (in the source, a neural network fitted by generalized least squares) whose partial derivatives are available at every grid point. Stack the values of $\hat u_t$ into a vector and the candidate right-hand-side terms into the columns of a library matrix

$$\Theta = \bigl[\, u_x,\ u_{xx},\ u,\ u^2,\ u u_x,\ u^2 u_x,\ u u_{xx},\ u^2 u_{xx},\ u_x^2,\ u u_x^2 \,\bigr]. \tag{10}$$

**Model.** A candidate equation is a coefficient vector $\xi$ with

$$u_t = \Theta\, \xi, \tag{11}$$

the nonzero entries of $\xi$ naming the terms present. For example, $\xi = (0, D, r, -r, 0, \dots, 0)$ is the Fisher–KPP equation $u_t = D u_{xx} + r u(1 - u)$.

**Sparse selection.** $\xi$ is estimated by a greedy forward–backward sparse regression with a tolerance chosen on a held-out half of the grid, followed by pruning: a term $i$ is retained only if deleting it (refitting without column $i$) raises the residual $\|u_t - \Theta\xi\|_2^2$ by at least a fixed fraction (5% in the source). Repeating over random training/validation splits and keeping the most frequent forms gives candidate models, among which one is chosen by AIC after forward simulation from the first time sample.

**Facts used in post-processing and estimation.**

1. *Conservation form.* $u_{xx} = (u_x)_x$, $u_x^2 + u u_{xx} = (u u_x)_x$ and $2u u_x^2 + u^2 u_{xx} = (u^2 u_x)_x$. Hence, for a quadratic diffusivity $D(u) = a + bu + cu^2$, one has $\bigl(D(u)u_x\bigr)_x = a\,u_{xx} + b\,\bigl(u_x^2 + u u_{xx}\bigr) + c\,\bigl(2u u_x^2 + u^2 u_{xx}\bigr)$, so a learned second-order transport part $\xi_{u_{xx}} u_{xx} + \xi_{u_x^2} u_x^2 + \xi_{u u_{xx}} u u_{xx} + \xi_{u u_x^2} u u_x^2 + \xi_{u^2 u_{xx}} u^2 u_{xx}$ has this flux form exactly when $\xi_{u_x^2} = \xi_{u u_{xx}}$ and $\xi_{u u_x^2} = 2\xi_{u^2 u_{xx}}$. Restricted to the two terms $u_x^2$ and $u u_{xx}$, flux form holds exactly when their coefficients are equal; in post-processing an isolated $u_x^2$ term is removed and the pair $u_x^2$, $u u_{xx}$ is kept when both are recovered.
2. *Known form.* If $u$ solves $u_t = D u_{xx} + r u(1-u)$ exactly, then with the two-column library $\Theta = [u(1-u),\ u_{xx}]$ the least-squares problem $\min_\xi \|u_t - \Theta\xi\|_2$ has residual $0$ at $\xi = (r, D)$, and this minimizer is unique whenever the two columns are linearly independent on the sampled points. Parameters are thus estimated without solving the PDE; uncertainty is quantified by repeating the fit on random half-samples of the grid (subagging).

## Expansion

The product rule gives $(u u_x)_x = u_x^2 + u u_{xx}$ and $(u^2u_x)_x = 2uu_x^2 + u^2u_{xx}$. The regression needs only the form of the Fisher–KPP equation, not results about its [travelling waves](../../pattern-formation/fisher-kpp-travelling-waves/README.md). In part 2 the residual vector vanishes at $(r, D)$, and the normal equations $\Theta^\top\Theta \xi = \Theta^\top u_t$ have a unique solution exactly when $\Theta$ has full column rank. With few time samples or noisy data the estimated derivatives are biased, which is why pruning and repeated splitting are needed in practice.

## Sources

- J. T. Nardini, J. H. Lagergren, A. Hawkins-Daarud, L. Curtin, B. Morris, E. M. Rutter, K. R. Swanson and K. B. Flores, *Learning equations from biological data with limited time samples*, Bull. Math. Biol. 82 (2020), 119, <https://doi.org/10.1007/s11538-020-00794-z>, PMCID PMC8409251 (Sections 2.2–2.4; equations (10) and (11)).
