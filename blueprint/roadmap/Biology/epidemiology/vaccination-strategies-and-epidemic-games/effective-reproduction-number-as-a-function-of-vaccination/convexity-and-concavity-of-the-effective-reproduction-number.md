# Convexity and concavity of the effective reproduction number in the vaccination strategy

**Setting.** In a population with $N$ groups (or a continuum of types), let $K \ge 0$ be the next-generation matrix (or a positive compact next-generation operator $T$ on $L^p(\mu)$, $p \in [1,\infty)$, such as an integral operator with kernel). A **vaccination strategy** is $\eta \in \Delta = [0,1]^N$ (resp. a measurable $\eta : \Omega \to [0,1]$), where $\eta_i$ is the fraction of group $i$ left unvaccinated (all-or-nothing vaccine). The **effective reproduction number** is the spectral radius

$$R_e(\eta) = \rho\big(K\,\mathrm{Diag}(\eta)\big) = \rho\big(\mathrm{Diag}(\eta)\,K\big), \qquad \text{resp. } R_e(\eta) = \rho(T M_\eta),$$

with $M_\eta$ multiplication by $\eta$. Basic properties: $R_e(0) = 0$, $R_e(\mathbf{1}) = R_0$, $R_e$ is non-decreasing and positively homogeneous, $R_e(\lambda\eta) = \lambda R_e(\eta)$ for $\lambda \in [0,1]$. A matrix is **diagonally symmetrizable** if $d_iK_{ij} = d_jK_{ji}$ for some positive $d_1,\dots,d_N$ (equivalently $\mathrm{Diag}(d)K$ is symmetric); then its spectrum is real. For a compact operator let $\mathrm{p}(T)$ and $\mathrm{n}(T)$ be the numbers of eigenvalues with positive, resp. negative, real part counted with algebraic multiplicity.

**Theorem (matrices).** Let $K \ge 0$ be diagonally symmetrizable with eigenvalues $\lambda_1 \ge \lambda_2 \ge \dots \ge \lambda_N$ (so $\lambda_1 = R_0$).

1. If $\lambda_N \ge 0$ (all eigenvalues non-negative), then $R_e$ is convex on $[0,1]^N$.
2. If $\lambda_2 \le 0$ (i.e. $R_0$ is a simple eigenvalue and all others are non-positive), then $R_e$ is concave on $[0,1]^N$.

**Theorem (operators).** Let $T$ be a positive compact diagonally symmetrizable operator on $L^p(\mu)$. If $\mathrm{n}(T) = 0$ then $R_e$ is convex; if $\mathrm{p}(T) = 1$ then $R_e$ is concave. Diagonal symmetrizability holds for integral operators $u \mapsto f(x)\int k(x,y)g(y)u(y)\,\mu(dy)$ with symmetric kernel $k$ and positive weights $f, g$ under integrability conditions, and the inertia $(\mathrm{p}(T),\mathrm{n}(T))$ is invariant under $T \mapsto M_fTM_g$ for positive bounded $f, g$ bounded away from $0$ (Sylvester's law of inertia).

**Invariance.** $R_e[M_hT] = R_e[TM_h]$ for non-negative $h$ and $R_e[M_hTM_{1/h}] = R_e[T]$ for positive $h$; hence models that differ by such transformations (for instance, kernels written with susceptibility on the left or infectiousness on the right) have the same $R_e$ function and the same optimal vaccination strategies. For a reducible operator split into irreducible components $T_i$, $R_e[T] = \max_i R_e[T_i]$.

## Expansion

If $\mathrm{Diag}(d)K = S$ is symmetric, then $\mathrm{Diag}(\eta)K$ is similar to the symmetric matrix $\mathrm{Diag}(\sqrt{\eta/d})\,S\,\mathrm{Diag}(\sqrt{\eta/d})$, so $R_e(\eta)$ is its largest eigenvalue and has a Rayleigh-quotient representation. When $S$ is positive semidefinite this representation becomes a supremum of functions that are linear in $\eta$, giving convexity; when $S$ has exactly one positive eigenvalue, a dual (inverse) variational formula applies and gives concavity. These eigenvalue-sign conditions are exactly the ones preserved by the congruences $T \mapsto M_fTM_g$ (Sylvester's law of inertia), which is why they transfer to all equivalent models. The operator case is obtained from the matrix case by finite-rank approximation and continuity of the spectrum. Convexity or concavity of $R_e$ is what decides the shape of optimal vaccine allocations under a dose budget, the question that motivates the result.

## Sources

- Jean-François Delmas, Dylan Dronnier and Pierre-André Zitt, "The effective reproduction number: convexity, concavity and invariance", arXiv:2211.11862 (2022), Theorems 1.1 and 1.2 (stated as Theorems 4.1 and 4.10), Proposition 2.3, Section 3 (spectrum-preserving transformations), Propositions 4.4 and 4.9, Corollaries 4.8 and 5.4, <https://doi.org/10.48550/arXiv.2211.11862>. Published version: Journal of the European Mathematical Society 27 (2024) 3249–3274, <https://doi.org/10.4171/jems/1431>.
