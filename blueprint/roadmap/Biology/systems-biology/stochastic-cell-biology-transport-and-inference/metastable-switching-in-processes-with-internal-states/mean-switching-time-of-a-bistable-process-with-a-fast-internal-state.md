# Mean switching time of a bistable process with a fast internal state

**Setting.** Let $S(t)$ be an internal state on $\{0,\dots,M-1\}$ that, for fixed external state $X = x$, jumps according to $\partial_t \mathbf{w} = \alpha_i A(x)\mathbf{w}$, where $A(x)$ is an irreducible transition-rate matrix (columns summing to zero, non-negative off-diagonal entries), so that it has a unique positive quasi-steady-state distribution $\rho(\cdot \mid x)$ with $A\rho = 0$. In the semi-continuous version the external state solves

$$dX(t) = -v(S(t), X(t))\,dt + \sqrt{b(S(t),X(t))/\alpha_e}\,dW(t),$$

with large parameters $\alpha_i, \alpha_e$ and small parameter $\epsilon = 1/\alpha_i$ (fast switching is a fixed multiple of the weak-noise scale). Assume the averaged drift $\bar v(x) = \sum_s \rho(s\mid x)v(s,x)$ makes the deterministic limit bistable, with stable points $x_- < x_+$ separated by an unstable point $x_*$. Let $T_\pm$ be the mean time to reach $x_*$ from $x_\pm$.

**WKB eigenfunction.** With $h(s,x,p) = p\,v(s,x) + p^2 b(s,x)$, define the Hamiltonian

$$\mathcal{H}(x,p) = \det\big(A(x) + \operatorname{diag}\mathbf{h}(x,p)\big).$$

The quasi-stationary density has the form $\mathbf{p}(x) \sim \hat{\mathbf{w}}(x)\exp\{-\Phi(x)/\epsilon - \Psi(x)\}$, where $p = \Phi'(x)$ is the non-trivial root of $\mathcal{H}(x,p) = 0$ for which $A + \operatorname{diag}\mathbf{h}$ has a positive null vector $\hat{\mathbf{w}}(x)$ (normalized to sum to one, and equal to $\rho(\cdot\mid x)$ at fixed points), $\Phi'' = -\mathcal{H}_x/\mathcal{H}_p$, and the pre-exponential factor $k(x) = e^{-\Psi(x)}$ is fixed at next order by a solvability condition with the left null vector of $A + \operatorname{diag}\mathbf{h}$.

**Theorem (principal eigenvalue).** With an absorbing boundary at $x_*$, the principal eigenvalue on either side satisfies

$$\lambda_\pm \sim \frac{B}{\pi}\sqrt{|\Phi''(x_*)|\,\Phi''(x_\pm)}\;\frac{k(x_*)}{k(x_\pm)}\exp\Big\{-\frac{1}{\epsilon}\big(\Phi(x_*) - \Phi(x_\pm)\big)\Big\}, \qquad B = \sum_s \rho(s\mid x_*)\big(b(s,x_*) - v(s,x_*)\zeta(s)\big),$$

where $\zeta$ is the vector correction of the adjoint eigenfunction in the boundary layer at $x_*$. The escape time is asymptotically exponential with mean $T_\pm \sim 1/\lambda_\pm$. The same structure, with a modified Hamiltonian, holds when the external state is a discrete birth–death count, as in a self-activating gene whose protein copy number switches between low and high expression.

## Expansion

Away from the fixed points, substituting the WKB ansatz into the forward Chapman–Kolmogorov equation gives at leading order $[A + \operatorname{diag}\mathbf{h}(x,\Phi')]\mathbf{r}_0 = 0$, whose solvability is $\mathcal{H}(x,\Phi') = 0$; positivity of $\mathbf{r}_0$ selects the physical branch, which is the large-deviation quasi-potential. Near $x_*$ the adjoint eigenfunction (the splitting probability) has a boundary layer of width $\epsilon^{1/2}$ described by an error-function profile plus fast internal-state corrections $\zeta$. Since the absorbing-boundary eigenvalue is exponentially small, the spectral projection formula $\lambda = (\text{flux at } x_*)/(\text{mass near } x_\pm)$ applies; Laplace's method around $x_\pm$ and the boundary-layer flux at $x_*$ produce the curvature prefactor $\sqrt{|\Phi''(x_*)|\Phi''(x_\pm)}/\pi$, the effective diffusivity $B$ and the ratio of pre-exponential factors, a generalization of the Kramers formula to processes with internal states.

## Sources

- Jay Newby, Jon Chapman, "Metastable behavior in Markov processes with internal states", Journal of Mathematical Biology 69 (2014), 941–976, <https://doi.org/10.1007/s00285-013-0723-1>. Published version of arXiv:1304.6957, cited next; locators there refer to the arXiv version.
- Jay Newby, Jon Chapman, "Metastable behavior in Markov processes with internal states", arXiv (2013). Section 2 (coupled processes), Section 3 (WKB expansion, Hamiltonian, eigenfunction theorem, principal-eigenvalue theorem, Equations for $\Phi''$, $\Psi'$ and $B$), Section 4 (gene expression example). <https://doi.org/10.48550/arXiv.1304.6957>
