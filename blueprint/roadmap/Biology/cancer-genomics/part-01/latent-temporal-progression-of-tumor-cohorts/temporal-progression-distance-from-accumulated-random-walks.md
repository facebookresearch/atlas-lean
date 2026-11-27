# Temporal progression distance from accumulated random walks

**Setting.** A cohort $\Omega$ of $N$ tumor samples has expression profiles $T_x \in \mathbb{R}^G$ and ordinal stages or grades $G_x \in \{1, 2, 3, 4, \dots\}$.

1. *Stage-weighted, locally scaled Gaussian kernel:*

$$S(x, y) = \exp\!\big(-\gamma_{xy} \|T_x - T_y\|^2\big), \qquad \gamma_{xy} = \frac{\omega_{xy}}{\varepsilon_x^2 + \varepsilon_y^2}, \qquad \omega_{xy} = 1 + |G_x - G_y|,$$

with $\varepsilon_x$ the distance from $x$ to its $\kappa$-th nearest neighbor.
2. *Density normalization:* $D(x) = \sum_{y} S(x, y)$ and $H_{xy} = S(x,y)/\big(D(x)D(y)\big)$.
3. *Symmetric transition matrix:* $E(x) = \sum_y H_{xy}$ and $P_{xy} = E(x)^{-1/2} H_{xy} E(y)^{-1/2}$.
4. *Accumulated transitions:* with $\psi_0$ the unit eigenvector of $P$ for eigenvalue $1$ and $\tilde P = P - \psi_0\psi_0^{\mathsf T}$,

$$Q = \sum_{t=1}^{\infty} \tilde P^{\,t} = (I - \tilde P)^{\dagger} - I .$$

5. *Temporal progression distance (TPD)* and progression score:

$$\mathrm{TPD}(x, y) = \big\| Q(x, \cdot) - Q(y, \cdot) \big\|_{2}, \qquad s(x) = \mathrm{TPD}(x_0, x),$$

with root $x_0 = \arg\max_{x \in \{x_{\min}\}} \mathrm{TPD}(x, x_{\mathrm{ref}})$ chosen among lowest-stage samples as farthest from a reference sample $x_{\mathrm{ref}}$ of maximal stage.

**Statement.** Because every $S(x, y) > 0$, the matrix $P$ is symmetric with strictly positive entries, its largest eigenvalue is $1$ and simple with eigenvector $\psi_0 \propto (E(x)^{1/2})_x$, and all other eigenvalues lie in $(-1, 1)$. Consequently $\tilde P$ has spectral radius $< 1$, the series defining $Q$ converges, $I - \tilde P$ is invertible, and

$$Q = (I - \tilde P)^{-1} - I = \sum_{k \ge 1} \frac{\lambda_k}{1 - \lambda_k}\, \psi_k \psi_k^{\mathsf T},$$

where $(\lambda_k, \psi_k)_{k \ge 1}$ are the remaining eigenpairs of $P$. TPD is thus a Euclidean distance in a diffusion-map embedding summed over all time scales, with no free time parameter, and the ordering of $s(x)$ gives a latent temporal progression of the cohort.

## Expansion

$P = E^{-1/2} H E^{-1/2}$ is similar to $E^{-1} H$, a row-stochastic matrix with positive entries, so by Perron–Frobenius its spectrum is real (by symmetry), contains $1$ as a simple eigenvalue, and every other eigenvalue has modulus $< 1$; the Perron eigenvector of $E^{-1}H$ is the constant vector, which maps to $E^{1/2}\mathbf 1$ for $P$. Removing the stationary projector $\psi_0\psi_0^{\mathsf T}$ replaces the eigenvalue $1$ by $0$ and leaves the others, so $\rho(\tilde P) < 1$, the Neumann series $\sum_{t \ge 0} \tilde P^{\,t} = (I - \tilde P)^{-1}$ converges, the Moore–Penrose inverse equals the ordinary inverse, and subtracting the $t = 0$ term gives $Q$. Diagonalizing, $\sum_{t\ge1}\lambda_k^t = \lambda_k/(1-\lambda_k)$. Rows $Q(x, \cdot)$ are the accumulated visit profiles from $x$, so two samples are close in TPD when random walks from them visit the cohort similarly at every scale.

## Sources

- X. Sun, J. Zhang, Q. Nie, "Inferring latent temporal progression and regulatory networks from cross-sectional transcriptomic data of cancer samples", *PLoS Computational Biology* 17(3) (2021) e1008379. Methods, "Similarity graph-based random walk" construction: Eqs. (1)–(9). <https://doi.org/10.1371/journal.pcbi.1008379>. PMCID: PMC7968745.
