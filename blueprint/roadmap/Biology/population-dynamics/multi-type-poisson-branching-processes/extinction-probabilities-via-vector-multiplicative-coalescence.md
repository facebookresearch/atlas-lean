# Extinction probabilities of multi-type Poisson branching processes via vector multiplicative coalescence

**Multi-type branching.** For a positively regular, nonsingular multi-type Galton–Watson process with $k$ types, offspring generating functions $f_i(\mathbf s)$ and mean matrix $\mathbf M$ with spectral radius $\rho(\mathbf M)$, the vector $\boldsymbol\eta$ of extinction probabilities (starting from one individual of each type) equals $\mathbf 1$ if $\rho(\mathbf M) \le 1$, and is the componentwise smallest solution in $[0,1)^k$ of $f_i(\mathbf s) = s_i$, $i = 1,\dots,k$, if $\rho(\mathbf M) > 1$. In a **multi-type Poisson** process an individual of type $i$ has independent $\mathrm{Poisson}(m_{ij})$ children of each type $j$, so $f_i(\mathbf s) = \exp\big(\sum_j m_{ij}(s_j - 1)\big)$.

**Vector multiplicative coalescent.** Clusters carry size vectors $\mathbf x \in \mathbb{N}_0^k$ (numbers of particles of each type). With a nonnegative, irreducible, symmetric $k \times k$ matrix $V$ and initial type proportions $\boldsymbol\alpha \in (0,\infty)^k$, two clusters of sizes $\mathbf x, \mathbf y$ merge at rate $\langle\mathbf x | V | \mathbf y\rangle = \mathbf x^{\top}V\mathbf y$. In the large-population limit the fractions $\zeta_{\mathbf x}(t)$ of clusters of size $\mathbf x$ solve the (modified) Smoluchowski coagulation equations, and **gelation** is the loss of mass to a giant cluster.

**Theorem (gelation).** (a) If $\rho(V D[\boldsymbol\alpha]\,t) \le 1$ the total mass $\sum_{\mathbf x}\zeta_{\mathbf x}(t)\,\mathbf x$ equals $\boldsymbol\alpha$; (b) if $\rho(V D[\boldsymbol\alpha]\,t) > 1$ it is strictly smaller. Hence the gelation time is
$$T_{\mathrm{gel}} = \frac{1}{\rho\big(V D[\boldsymbol\alpha]\big)},$$
where $D[\boldsymbol\alpha]$ is the diagonal matrix of $\boldsymbol\alpha$.

**Theorem (correspondence and series).** The post-gelation mass equations of the coalescent coincide with the extinction equations of the multi-type Poisson branching process with mean matrix $\mathbf M = V D[\boldsymbol\alpha]\,t$: by the multidimensional Lambert–Euler inversion, $y_i e^{-\langle\mathbf e_i|V|\mathbf y\rangle} = \alpha_i t\,e^{-\langle\mathbf e_i|V|\boldsymbol\alpha t\rangle}$ has a unique solution $\mathbf y$ in the subcritical region, equal to $\boldsymbol\alpha t$ before gelation and strictly smaller after it, and this smallest solution is what determines both the post-gelation mass and the extinction vector. Consequently the extinction probabilities of a multi-type Poisson branching process whose mean matrix factors as $\mathbf M = V D[\boldsymbol\alpha]\,t$ (with $V$ symmetric, nonnegative and irreducible) have an explicit convergent series expansion
$$\eta_\ell = \frac{1}{\alpha_\ell}\sum_{\mathbf x}\frac{\boldsymbol\alpha^{\mathbf x}}{\mathbf x!\,\mathbf x^{\mathbf 1}}\;\tau\Big(K_k,\ x_i x_j\frac{m_{ij}}{\alpha_j}\Big)\,\big(\mathbf M D[\alpha_i^{-1}]\mathbf x\big)^{\mathbf x - \mathbf 1}\,e^{-\langle\mathbf x|\mathbf M|\mathbf 1\rangle}\,x_\ell,$$
where $\tau(K_k, w_{ij})$ is the weighted spanning-tree polynomial of the complete graph $K_k$ (multi-index powers are taken componentwise).

## Expansion

Both problems are governed by the same random graph: the clusters of the coalescent at time $t$ are the components of an inhomogeneous random graph in which particles of types $i, j$ are linked with probability proportional to $V_{ij}t$, and exploring a component from one particle is, in the limit, a multi-type Poisson branching process with means $V_{ij}\alpha_j t$. A finite component corresponds to extinction, so the mass outside the giant component equals the extinction probability, and the gel appears exactly when the branching process becomes supercritical, $\rho(V D[\boldsymbol\alpha]t) > 1$. Counting the trees that span finite components gives the series via a multi-type Cayley formula.

## Sources

- Heshan Aravinda, Yevgeniy Kovchegov, Peter T. Otto and Amites Sarkar, "Gelation in Vector Multiplicative Coalescence and Extinction in Multi-Type Poisson Branching Processes", arXiv:2409.06910 (2024), Theorems 2.1, 3.1, 4.1, 5.1 and 5.3, <https://doi.org/10.48550/arXiv.2409.06910>.
