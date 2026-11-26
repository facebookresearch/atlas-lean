# Convexity and concavity of the effective reproduction number in the vaccination profile

**Setting.** In a metapopulation epidemic model (SIS, SIR, SEIR, …) with $N$ subpopulations and next-generation matrix $K\ge0$, a perfect-vaccine strategy is a vector $\eta\in[0,1]^N$ giving the *non-vaccinated* fraction of each subpopulation, and the effective reproduction number is

$$R_e(\eta)=\rho\big(K\,\mathrm{diag}(\eta)\big),$$

the spectral radius of the effective next-generation matrix. More generally, for a kernel $\mathsf k$ on a probability space $(\Omega,\mu)$ and $\eta:\Omega\to[0,1]$, $R_e(\eta)$ is the spectral radius of the integral operator $f\mapsto\int\mathsf k(\cdot,y)\eta(y)f(y)\,\mu(dy)$.

**Basic properties.** $R_e$ is continuous, $R_e(0)=0$, $R_e(\mathbf 1)=R_0$, $R_e$ is nondecreasing ($\eta_1\le\eta_2\Rightarrow R_e(\eta_1)\le R_e(\eta_2)$) and positively homogeneous: $R_e(\lambda\eta)=\lambda R_e(\eta)$ for $\lambda\in[0,1]$.

**Theorem (Hill–Longini conjecture for symmetrizable matrices).** Suppose $K$ is diagonally symmetrizable, i.e. there are $d_1,\dots,d_N>0$ with $d_iK_{ij}=d_jK_{ji}$; then $K$ has real eigenvalues $\lambda_1=R_0\ge\lambda_2\ge\dots\ge\lambda_N$.

- If $\lambda_N\ge0$ (all eigenvalues nonnegative), $R_e$ is convex on $[0,1]^N$.
- If $\lambda_2\le0$ ($R_0$ simple and all other eigenvalues nonpositive), $R_e$ is concave on $[0,1]^N$.

**Theorem (kernel version).** If $\mathsf k$ is strongly diagonally Hilbert–Schmidt ($\mathsf k(x,y)=f(x)\mathsf k'(x,y)g(y)$ with $\mathsf k'$ symmetric Hilbert–Schmidt and $f,g$ bounded and bounded away from $0$), then $R_e$ is convex if $T_{\mathsf k}$ has no negative eigenvalue, and concave if $T_{\mathsf k}$ has exactly one positive eigenvalue (counted with multiplicity).

Without the symmetry assumption the conjecture fails: real spectrum alone does not imply convexity or concavity.

## Expansion

For symmetric $S=D^{1/2}KD^{-1/2}$, $R_e(\eta)$ equals the largest eigenvalue of $\mathrm{diag}(\sqrt\eta)\,S\,\mathrm{diag}(\sqrt\eta)$, a Rayleigh quotient $\max_{\|x\|=1}\sum_{ij}S_{ij}\sqrt{\eta_i\eta_j}x_ix_j$. When $S$ is positive semidefinite, substituting $y=\sqrt\eta\, x$ gives $R_e(\eta)=\max_y\{\langle y,Sy\rangle:\sum y_i^2/\eta_i\le1\}$, a supremum of functions convex in $\eta$ (perspective functions), hence convex. When $S$ has one positive eigenvalue, the analogous min–max representation over the negative part yields concavity. Sylvester's inertia theorem ($M_fT'M_g$ has the same numbers of positive and negative eigenvalues as $T'$) transfers the sign conditions from the symmetric kernel $\mathsf k'$ to $\mathsf k$. Convexity matters because it makes Pareto-optimal vaccination profiles lie along rays (scalings) of one optimal strategy for affine costs.

## Sources

- Jean-François Delmas, Dylan Dronnier, Pierre-André Zitt, "Effective reproduction number: Convexity, invariance and cordons sanitaires", arXiv:2110.12693: Theorem 1.1 and Theorem 5.1 (matrix case), Proposition 3.5 (basic properties of $R_e$), Theorem 5.5 and Proposition 5.6 (kernel case), Theorem 5.10 (Sylvester's inertia theorem), Proposition 6.2 (optimal ray). <https://doi.org/10.48550/arXiv.2110.12693>
