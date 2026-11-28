# Generalized matrix decomposition and the GMD biplot

**Setting.** Let $X \in \mathbb R^{n \times p}$ be a column-centered data matrix of rank $K$ (for microbiome data: $n$ samples by $p$ taxa, e.g. after a centered log-ratio transform). Let $H \in \mathbb R^{n\times n}$ and $R \in \mathbb R^{p \times p}$ be positive semidefinite similarity kernels on samples and on variables. A typical sample kernel comes from a matrix $D$ of squared dissimilarities, such as squared UniFrac distances, via $H = -\tfrac12 J D J$ with $J = I_n - \tfrac1n \mathbf 1_n \mathbf 1_n^{\mathsf T}$; when $D$ holds squared Euclidean distances between rows, $H = XX^{\mathsf T}$. Define

$$\|X\|_{H,R}^2 = \operatorname{tr}(X R X^{\mathsf T} H).$$

**Generalized matrix decomposition (GMD).** For $q \le K$, the GMD solution is

$$(\tilde U, \tilde V, \tilde S) = \arg\min_{U,S,V} \|X - U S V^{\mathsf T}\|_{H,R}^2 \quad \text{s.t. } U^{\mathsf T} H U = I_q,\ V^{\mathsf T} R V = I_q,\ \operatorname{diag}(S) \ge 0,$$

with $S$ diagonal. For $H = I_n$, $R = I_p$ it is the truncated singular value decomposition.

**Proposition.** The GMD solution satisfies

$$\text{(a)}\ \ X R X^{\mathsf T} H \tilde U = \tilde U \tilde S^2, \qquad \text{(b)}\ \ \tilde V \tilde S = X^{\mathsf T} H \tilde U,$$

so the squared GMD values are eigenvalues of $XRX^{\mathsf T}H$ with eigenvectors the columns of $\tilde U$, and the right vectors follow from the left ones by duality.

**GMD biplot.** Take $R = I_p$ and let $v_1, v_2$ be the first two columns of $\tilde V$. Plot sample $i$ at $(x_i^{\mathsf T} v_1, x_i^{\mathsf T} v_2)$ and variable $j$ as the arrow $(e_j^{\mathsf T} v_1, e_j^{\mathsf T} v_2)$; a new sample $x^*$ is projected to $(x^{*\mathsf T} v_1, x^{*\mathsf T} v_2)$. The display explains the fraction $(\tilde\sigma_1^2 + \tilde\sigma_2^2)/\operatorname{tr}(XX^{\mathsf T}H)$ of $\|X\|_{H,I}^2$, where $\tilde\sigma_k$ are the GMD values in nonincreasing order. In the covariance form ($U^{\mathsf T}HU = I_q$, $V^{\mathsf T}V = I_q$), $\|X\|_{H,I}^2 = \sum_{m} s_m^2 = \sum_{j=1}^p \sum_m v_{jm}^2 s_m^2$, so $\sum_m v_{jm}^2 s_m^2 / \|X\|_{H,I}^2$ is the share of $H$-weighted variability attributable to variable $j$.

## Expansion

The SVD biplot implicitly uses the Euclidean kernel $XX^{\mathsf T} = -\tfrac12 J\Delta^E J$. Principal-coordinate plots built from a non-Euclidean kernel $H$ position samples but give no variable directions; an approximate-duality fix that keeps the PCoA sample vectors and fits $V$ by least squares can produce out-of-order "singular values", so the full decomposition is needed before choosing which axes to plot. The GMD instead optimizes a single criterion that weights the reconstruction error by $H$ (and optionally $R$, e.g. a phylogenetic kernel on taxa), keeps the values ordered, and so needs only $q = 2$ components. Since $X^{\mathsf T}HX$ and $XX^{\mathsf T}H$ share their nonzero spectrum, the GMD axes emphasize directions where the data covariance and the sample kernel are jointly large: a direction with small raw variance but large kernel eigenvalue can dominate, which is why the GMD biplot can separate sample groups that an approximate-duality biplot mixes.

## Sources

- Y. Wang, T. W. Randolph, A. Shojaie, J. Ma, "The generalized matrix decomposition biplot and its application to microbiome data", mSystems 4:e00504-19 (2019), Materials and Methods (Equation 3 and Proposition 1) and Discussion, <https://doi.org/10.1128/mSystems.00504-19>, PMCID PMC6918030.
