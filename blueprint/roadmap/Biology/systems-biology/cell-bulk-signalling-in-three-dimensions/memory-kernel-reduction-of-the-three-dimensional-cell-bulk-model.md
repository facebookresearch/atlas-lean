# Memory-kernel reduction of the three-dimensional cell-bulk model

**Model.** $N$ spherical cells $\Omega_{\varepsilon_j}=\{|x-x_j|\le\varepsilon\}$ in $\mathbb{R}^3$, well separated, exchange a signal $U$ that diffuses and decays in the bulk:
$$\partial_t U=D\Delta U-\sigma U\quad(x\notin\cup_j\Omega_{\varepsilon_j}),\qquad U(x,0)=0,\qquad \varepsilon D\,\partial_nU=d_{1j}U-\frac{d_{2j}}{\varepsilon}u_{1j}\ \text{on }\partial\Omega_{\varepsilon_j},$$
coupled to intracellular kinetics $\mathbf{u}_j=(u_{1j},\dots,u_{mj})$:
$$\frac{d\mathbf{u}_j}{dt}=\mathbf{F}_j(\mathbf{u}_j)+\frac{\mathbf{e}_1}{\varepsilon}\int_{\partial\Omega_{\varepsilon_j}}\Bigl(d_{1j}U-\frac{d_{2j}}{\varepsilon}u_{1j}\Bigr)dS .$$

**Reduction.** As $\varepsilon\to0$, for $t\gg O(\varepsilon^2)$,
$$\frac{d\mathbf{u}_j}{dt}=\mathbf{F}_j(\mathbf{u}_j)-\kappa_ju_{1j}\mathbf{e}_1+\frac{\varepsilon d_{1j}}{d_{2j}}\kappa_jB_j(t)\,\mathbf{e}_1,$$
$$B_j(t)=-\frac{\kappa_ju_{1j}(0)}{4\pi D^{3/2}}g(t)-\frac{\kappa_j}{4\pi D^{3/2}}\int_0^tu_{1j}'(\tau)g(t-\tau)\,d\tau+\sum_{k\ne j}\kappa_k\int_0^tu_{1k}(\tau)\,G(a_{jk},t-\tau)\,d\tau,$$
with self-interaction kernel $g(t)=\frac{e^{-\sigma t}}{\sqrt{\pi t}}+\sqrt\sigma\,\mathrm{erf}(\sqrt{\sigma t})$, free-space kernel $G(a,t)=\frac{e^{-\sigma t}e^{-a^2/(4t)}}{(4\pi Dt)^{3/2}}$, scaled distances $a_{jk}=|x_j-x_k|/\sqrt D$ and $\kappa_j=\frac{4\pi Dd_{2j}}{d_{1j}+D}$. The bulk field is $U(x,t)\sim\sum_j\kappa_j\int_0^tu_{1j}(\tau)G(|x-x_j|/\sqrt D,t-\tau)\,d\tau$.

**Consequences.**
1. *Steady states.* If the solution converges, the limits satisfy the nonlinear algebraic system $\mathbf{F}_j(\mathbf{u}_{j\infty})-\kappa_ju_{1j\infty}\mathbf{e}_1+O(\varepsilon)\,B_{j\infty}\mathbf{e}_1=0$, $B_{j\infty}=-\frac{\kappa_j}{D}R_0u_{1j\infty}-\sum_{k\ne j}\frac{\kappa_k}{D}u_{1k\infty}G_{0jk}$, with steady Green's function values $G_{0jk}$.
2. *Weak coupling.* Interaction with other cells enters only at $O(\varepsilon)$, unlike the stronger coupling of the two-dimensional cell-bulk model. Cells separated by $O(1)$ distances therefore synchronize only on time scales $O(\varepsilon^{-1})$.
3. *Linear stability.* Discrete eigenvalues of the linearization about a steady state are the roots of $\det\mathcal{M}(\lambda)=0$ for an explicit $N\times N$ matrix $\mathcal{M}(\lambda)=I+DP_1-4\pi\varepsilon\mathcal{G}_\lambda+4\pi DP_2\mathcal{H}(\lambda)$. For Sel'kov kinetics with a diagonalizable, constant-row-sum $\mathcal{G}_\lambda$ (e.g. cells on a ring), the Hopf threshold shifts from its isolated-cell value as $\alpha_c=\alpha_{cH}+\varepsilon\alpha_{1j}+O(\varepsilon^2)$, with $\alpha_{1j}$ given by the eigenvalues of $\mathcal{G}_\lambda$.

## Expansion

Near each cell the signal is a point-source field $\propto1/(\varepsilon\rho)$ plus a smooth background $B_j(t)$, and matching with the outer solution, a sum of time convolutions of the free-space heat kernel with decay, gives the self-interaction memory term (from the Laplace transform $\sqrt{s+\sigma}/s$, inverted to $g$) and the cross-interaction terms. Because the 3-D Green's function is bounded away from the source, the background seen by one cell from the others is $O(\varepsilon)$ relative to its own flux, hence weak coupling. Linearizing the reduced system and Laplace transforming converts the memory kernels into $\lambda$-dependent matrices, giving the determinant condition; a matrix perturbation expansion in $\varepsilon$ around the isolated-cell Hopf point yields the shifted thresholds. Long-time simulation uses a sum-of-exponentials approximation of the kernels.

## Sources

- M. Pelz, M. J. Ward, "Synchronized Memory-Dependent Intracellular Oscillations for a Cell-Bulk ODE-PDE Model in $\mathbb{R}^3$", arXiv:2611.32077 (2026), Section 2 (dimensionless cell-bulk model, Proposition 1), Propositions 2–4, <https://doi.org/10.48550/arXiv.2611.32077>.
