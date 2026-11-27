# Piecewise-constant spectral dynamics of the time-varying dynamic network

**Model.** Let $X(t) \in \mathbb R^d$ be the activity of $d$ brain regions on $t \in [0, T]$, observed with noise at times $t_1, \dots, t_n$ as $Y_j = X(t_j) + \epsilon_j$ with independent mean-zero errors $\epsilon_j$, and suppose

$$X'(t) = A(t) X(t), \qquad A(t) = U \Lambda(t) U^{-1},$$

where $U$ is a fixed invertible (possibly complex) matrix and $\Lambda(t)$ is diagonal. The eigenvalues are piecewise constant: for switching times $0 = \tau_0 < \tau_1 < \dots < \tau_M < \tau_{M+1} = T$,

$$\Lambda(t) = \Lambda_k \quad \text{for } \tau_{k-1} < t \le \tau_k, \qquad \Lambda_k \ne \Lambda_{k+1},$$

and $\operatorname{rank} A(t) = \operatorname{rank} \Lambda(t) \le r \ll d$ for all $t$, with the diagonal ordered so that $\lambda_{r+1}(t) = \dots = \lambda_d(t) = 0$ for all $t$ (the active modes are the same $r$ columns of $U$ in every segment). Columns of $U$ are stationary spatial modes; the switching times are brain-state switches. With $\Lambda$ constant the model is dynamic mode decomposition, and with $A = -\beta \mathcal L$ for a structural graph Laplacian $\mathcal L$ the unconstrained ODE $X' = AX$ is the network diffusion model (before the rank constraint, which a connected graph's Laplacian violates).

**Solution within a segment.** On segment $k$ with initial value $X_{0k} = X(\tau_{k-1})$, writing the $j$-th eigenvalue as $\lambda_j = \gamma_j + i\, 2\pi f_j$,

$$X(t) = U e^{\Lambda_k (t - \tau_{k-1})} U^{-1} X_{0k} = \sum_{j=1}^{r} U_j\, e^{(\gamma_j + i 2\pi f_j)(t - \tau_{k-1})}\, (U^{-1})_{j\cdot}\, X_{0k} + \sum_{j=r+1}^{d} U_j\, (U^{-1})_{j\cdot}\, X_{0k},$$

the last sum collecting the zero-eigenvalue modes, which are constant on the segment (the source's Eq. (3) omits it). The real part $\gamma_j$ is the growth or decay rate of mode $j$ on the segment and $f_j$ its oscillation frequency, in cycles per unit of $t$ (cycles per sampling interval when time is measured in sampling intervals).

**Solution across segments.** With $A_k = U \Lambda_k U^{-1}$, for $\tau_{k-1} < t \le \tau_k$,

$$X(t) = \exp\Big\{ \sum_{l=1}^{k-1} A_l (\tau_l - \tau_{l-1}) + A_k (t - \tau_{k-1}) \Big\} X(0).$$

This holds because all $A_l$ share the eigenvectors $U$ and therefore commute, so the product of the segment propagators is the exponential of the sum.

**Mode coordinates.** Let $\tilde X(t) = (U^{-1})_{r\cdot} X(t)$ be the coordinates of $X$ on the $r$ active modes. Then

$$\tilde X'(t) = \Lambda_{r \times r}(t)\, \tilde X(t),$$

a system of $r$ decoupled scalar equations $\tilde X_j' = \lambda_j(t) \tilde X_j$ with only $r$ unknown parameters per segment. Each coordinate is continuous in $t$; when $\tilde X_j(0) \ne 0$, $\log\lvert\tilde X_j\rvert$ is piecewise linear with slope $\operatorname{Re}\lambda_j(t)$, changing at $\tau_k$ exactly when $\operatorname{Re}\lambda_j$ changes there.

## Expansion

On a segment $A$ is constant, so the linear ODE is solved by the matrix exponential, and $e^{U\Lambda U^{-1} s} = U e^{\Lambda s} U^{-1}$ diagonalizes it into independent complex exponentials. Continuity of $X$ at each $\tau_k$ glues the segment solutions; since $e^{A_k s} e^{A_l s'} = e^{A_k s + A_l s'}$ for commuting $A_k, A_l$, the glued solution is a single exponential, which the source proves by induction over segments. Projecting the ODE with $(U^{-1})_{r\cdot}$ uses $A = U_{\cdot r} \Lambda_{r\times r} (U^{-1})_{r\cdot}$ for a rank-$r$ $A$. The fixed-eigenvector constraint encodes that spatial organization is set by stable anatomy while the coupling strength of each network changes, and the piecewise-constant eigenvalues encode abrupt switches between quasi-stable brain states.

## Sources

- F. Jiang, H. Jin, Y. Gao, X. Xie, J. Cummings, A. Raj, S. Nagarajan, "Time-varying dynamic network model for dynamic resting state functional connectivity in fMRI and MEG imaging", NeuroImage 254 (2022) 119131, Section 2.1, Eqs (1)–(3) and (5), and Eq (7) in the proof of Proposition 1 (Appendix E.2), <https://doi.org/10.1016/j.neuroimage.2022.119131>, PMCID PMC9942947.
