# Eigenfunction expansion of spatial balanced firing rates

**Setting.** Consider the [balanced-rate integral equations](balanced-firing-rates-as-a-fredholm-equation-of-the-first-kind.md) $\mathcal W\boldsymbol r+\boldsymbol F=0$ (infinite network) and $\mathcal W\boldsymbol r+\boldsymbol F=\epsilon D\boldsymbol r$ (finite-$N$ correction). The block operator $\mathcal W=\begin{bmatrix}\mathcal W_{ee}&\mathcal W_{ei}\\\mathcal W_{ie}&\mathcal W_{ii}\end{bmatrix}$ is not Hermitian even for symmetric kernels, because $w_{ei}\ne w_{ie}$, so standard diagonalization does not apply directly.

**Theorem.** Suppose each kernel is symmetric, $w_{ab}(x,y)=w_{ab}(y,x)$, $w_{ab}\in L^2(\Omega^2)$, and the four operators $\mathcal W_{ab}$ share an orthonormal eigenbasis $\{\phi_m\}$ of $L^2(\Omega)$ with eigenvalues $\mu_m^{ab}$. Let

$$\widetilde W_m=\begin{bmatrix}\mu_m^{ee}&\mu_m^{ei}\\\mu_m^{ie}&\mu_m^{ii}\end{bmatrix},\qquad\widetilde{\boldsymbol F}_m=\begin{bmatrix}\langle F_e,\phi_m\rangle\\\langle F_i,\phi_m\rangle\end{bmatrix}.$$

If $\epsilon\ne0$ and $\epsilon D-\widetilde W_m$ is nonsingular for all $m$, then

$$\boldsymbol r(x)=\sum_m[\epsilon D-\widetilde W_m]^{-1}\widetilde{\boldsymbol F}_m\,\phi_m(x)$$

converges in $L^2$ to a solution of the finite-$N$ equation. If the series converges at $\epsilon=0$, its sum solves the balance equation $\mathcal W\boldsymbol r+\boldsymbol F=0$.

**Corollary (separable kernels and inputs).** If $w_{ab}(x,y)=\bar w_{ab}k(x,y)$ and $F_a(x)=\bar F_aF(x)$, with $\mu_m,\phi_m$ the eigenpairs of $(\mathcal Kr)(x)=\int_\Omega k(x,y)r(y)\,dy$ and $\tilde F_m=\langle F,\phi_m\rangle$, the balanced rates are

$$\boldsymbol r(x)=-\overline W^{-1}\overline{\boldsymbol F}\sum_m\frac{\tilde F_m}{\mu_m}\phi_m(x)$$

whenever the series converges, with $\overline W=(\bar w_{ab})$ and $\overline{\boldsymbol F}=(\bar F_e,\bar F_i)$; the excitatory–inhibitory and spatial parts separate. Terms with $\mu_m=0$ require $\tilde F_m=0$. At finite $N$, $\boldsymbol r(x)=\sum_m[\epsilon D-\overline W\mu_m]^{-1}\overline{\boldsymbol F}\tilde F_m\phi_m(x)$.

## Depends on

- [Balanced firing rates as a Fredholm equation of the first kind](balanced-firing-rates-as-a-fredholm-equation-of-the-first-kind.md)

## Expansion

Because $\mu_m^{ab}\to0$, the matrices $\epsilon D-\widetilde W_m$ tend to $\epsilon D$, so for $\epsilon\ne0$ the series converges whenever $\sum_m\widetilde{\boldsymbol F}_m\phi_m$ does, i.e. always. Projecting the series onto each $\phi_m$ shows $\langle\epsilon D\boldsymbol r-\mathcal W\boldsymbol r,\phi_m\rangle=\langle\boldsymbol F,\phi_m\rangle$ for all $m$, and completeness of the basis gives the equation. At $\epsilon=0$ convergence is an extra requirement, the Picard condition: with every $\widetilde W_m$ invertible, the series converges in $L^2$ iff $\sum_m\|\widetilde W_m^{-1}\widetilde{\boldsymbol F}_m\|^2<\infty$ (in the separable case $\sum_m|\tilde F_m/\mu_m|^2<\infty$), because $\{\phi_m\}$ is orthonormal. Shared eigenbases arise for kernels that are multiples of one kernel and for periodic convolution kernels (Fourier modes).

## Sources

- C. Ebsch, R. Rosenbaum, "Spatially extended balanced networks without translationally invariant connectivity", Journal of Mathematical Neuroscience 10 (2020), section "Mean field theory of balance in spatially extended networks without translational invariance": Theorem 1 and its proof, Corollary 1, Equations (11)–(13), <https://doi.org/10.1186/s13408-020-00085-w>, PMCID PMC7221049.
