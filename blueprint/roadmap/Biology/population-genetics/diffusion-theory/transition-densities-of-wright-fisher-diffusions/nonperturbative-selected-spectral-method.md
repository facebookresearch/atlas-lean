# Nonperturbative spectral method for general diploid selection

Song and Steinrücken (2012) compute the eigenvalues and eigenfunctions of the Wright–Fisher generator with recurrent mutation and general diploid selection, $L = L_0 + 2\sigma x(1 - x)[x + h(1 - 2x)]\partial_x$, as follows. With the mean fitness function $\bar\sigma(x) = 2\sigma x[x + 2h(1 - x)]$ and the Jacobi polynomials $R_m$, orthogonal for the neutral speed density $\pi_0(x) = x^{\alpha - 1}(1 - x)^{\beta - 1}$ and satisfying $L_0R_m = -\lambda_mR_m$, the functions $K_m = e^{-\bar\sigma/2}R_m$ satisfy the boundary conditions of the selected diffusion and $LK_m = -e^{-\bar\sigma/2}(\lambda_m + Q)R_m$ for a degree-four polynomial $Q$. Writing an eigenfunction as $B_n = \sum_mw_{n,m}K_m$ and expanding $QR_m = \sum_{i=-4}^4b_m^{(i)}R_{m+i}$ by the three-term recurrence of the Jacobi polynomials turns $LB_n = -\Lambda_nB_n$ into the infinite linear eigenproblem $Mw_n = \Lambda_nw_n$, whose matrix $M$ has nonzero entries only in the nine central diagonals; for genic selection ($h = \frac12$) the coefficients $b_m^{(\pm3)}$ and $b_m^{(\pm4)}$ vanish and only five diagonals remain (their Algorithms 1 and 2 and equation (37)). Truncating $M$ to its leading $D \times D$ block $M^{[D]}$ gives approximations $\Lambda_n^{[D]}$ and $w_n^{[D]}$, which their empirical results show converge very rapidly as $D$ increases; they caution that for strong selection the exponential weights in the speed density and the basis functions require the coefficients to be computed with high precision. The transition density is then the spectral sum $p(t; x, y) = \sum_ne^{-\Lambda_nt}\pi(y)B_n(x)B_n(y)/\langle B_n, B_n\rangle_\pi$ (their equation (5)). The truncation $M^{[D]}$ is the Galerkin approximation of $-L$ on the span of $K_0, \dots, K_{D-1}$; its convergence is supported by their computations, and rates are a separate question.

## Depends on

- [Transition density of the Wright–Fisher diffusion with diploid selection](../../../../Biology/population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/transition-density-with-diploid-selection.md)
- [Weak-selection perturbation of the Wright–Fisher spectrum](../../../../Biology/population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/kimura-selection-perturbation.md)
- [Jacobi eigenbasis of the Wright–Fisher generator with mutation](../wright-fisher-diffusion-with-mutation/jacobi-eigenbasis-with-mutation.md)

## Expansion

1. The diploid-selection generator, its speed density $e^{\bar\sigma}\pi_0$, and the basis $K_m = e^{-\bar\sigma/2}R_m$.
2. The expansion of $QR_m$ in Jacobi polynomials and the nine-diagonal matrix $M$, five-diagonal for genic selection.
3. The truncated eigenproblem $M^{[D]}w = \Lambda w$ as a Galerkin approximation, and convergence of $\Lambda_n^{[D]}$ to $\Lambda_n$ by the min–max principle.
4. Error bounds for the truncated spectral sum of the transition density at positive times.

## Sources

- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, Genetics 190 (2012), 1117–1129, Background (equation (5)), Algorithms 1 and 2, equations (29)–(37), and Empirical Results. <https://doi.org/10.1534/genetics.111.136929>
