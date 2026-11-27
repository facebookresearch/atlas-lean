# Two-locus Wright–Fisher diffusion with selection and an explicit diffusion coefficient

Consider a diploid, randomly mating population of $N$ individuals at two loci $A$ and $B$ with recombination fraction $r$, alleles $A_1, A_2$ and $B_1, B_2$, and haplotypes $1 = A_1B_1$, $2 = A_1B_2$, $3 = A_2B_1$, $4 = A_2B_2$. Viability selection acts multiplicatively across loci; at locus $A$ the genotypes $A_1A_1$, $A_1A_2$, $A_2A_2$ have relative viabilities $1$, $1 - h_A s_A$, $1 - s_A$ (similarly at $B$), with $s_A, s_B, h_A, h_B \in [0, 1]$. Rescale time by $2N$ and let $N \to \infty$ with $\alpha_A = 2Ns_A$, $\alpha_B = 2Ns_B$ and $\rho = 4Nr$ fixed.

**Model (He, Dai, Beaumont and Yu 2020, Eqs. 1–5).** The haplotype frequencies $X(t) = (X_1, \dots, X_4)$ in the simplex $\Omega_X = \{x \in [0,1]^4 : \sum_i x_i = 1\}$ solve

$$dX(t) = \mu(X(t))\, dt + \sigma(X(t))\, dW(t),$$

with $W$ a six-dimensional standard Brownian motion. Writing $p_A = x_1 + x_2$, $p_B = x_1 + x_3$, $\eta_A(x) = p_A h_A + (1 - p_A)(1 - h_A)$, $\eta_B(x) = p_B h_B + (1 - p_B)(1 - h_B)$ and $D(x) = x_1x_4 - x_2x_3$, the drift is

$$\begin{aligned}
\mu_1 &= \alpha_A x_1 (1 - p_A)\eta_A + \alpha_B x_1 (1 - p_B)\eta_B - \tfrac{\rho}{2} D, &
\mu_2 &= \alpha_A x_2 (1 - p_A)\eta_A - \alpha_B x_2\, p_B\, \eta_B + \tfrac{\rho}{2} D,\\
\mu_3 &= -\alpha_A x_3\, p_A\, \eta_A + \alpha_B x_3 (1 - p_B)\eta_B + \tfrac{\rho}{2} D, &
\mu_4 &= -\alpha_A x_4\, p_A\, \eta_A - \alpha_B x_4\, p_B\, \eta_B - \tfrac{\rho}{2} D,
\end{aligned}$$

and the $4 \times 6$ diffusion coefficient, with one column per unordered pair of haplotypes $\{1,2\}, \{1,3\}, \{1,4\}, \{2,3\}, \{2,4\}, \{3,4\}$, is

$$\sigma(x) = \begin{pmatrix}
\sqrt{x_1x_2} & \sqrt{x_1x_3} & \sqrt{x_1x_4} & 0 & 0 & 0\\
-\sqrt{x_2x_1} & 0 & 0 & \sqrt{x_2x_3} & \sqrt{x_2x_4} & 0\\
0 & -\sqrt{x_3x_1} & 0 & -\sqrt{x_3x_2} & 0 & \sqrt{x_3x_4}\\
0 & 0 & -\sqrt{x_4x_1} & 0 & -\sqrt{x_4x_2} & -\sqrt{x_4x_3}
\end{pmatrix}.$$

**Proposition.** $\sigma(x)\sigma(x)^{\top} = \Sigma(x)$ with $\Sigma_{ii} = x_i(1 - x_i)$ and $\Sigma_{ij} = -x_ix_j$ ($i \ne j$), the Wright–Fisher infinitesimal covariance. Hence this SDE has the same generator

$$\mathcal{L} = \sum_{i=1}^4 \mu_i(x)\frac{\partial}{\partial x_i} + \frac12\sum_{i=1}^4\sum_{j=1}^4 \Sigma_{ij}(x)\frac{\partial^2}{\partial x_i\, \partial x_j}$$

as the formulation with a $4 \times 3$ square root of $\Sigma$, while avoiding a Cholesky factor that is singular on the boundary of the simplex. Each column moves mass between one pair of haplotypes, so $\sum_i dX_i = 0$ and the simplex constraint is preserved.

## Depends on

- [Generator of the two-locus Wright–Fisher diffusion](../../coalescent-theory/two-locus-coalescent/two-locus-generator.md)

## Proof depends on

- [Generator of the two-locus Wright–Fisher diffusion](../../coalescent-theory/two-locus-coalescent/two-locus-generator.md)

## Expansion

The marginal fitness difference between $A_1$ and $A_2$ under the viabilities $1, 1 - h_As_A, 1 - s_A$ is $s_A[p_A h_A + (1 - p_A)(1 - h_A)] = s_A \eta_A$, so selection at $A$ changes each $A_1$-carrying haplotype frequency at rate $\alpha_A x_i (1 - p_A)\eta_A$ and each $A_2$-carrying one at rate $-\alpha_A x_i p_A \eta_A$; locus $B$ is analogous and recombination moves frequency $\tfrac{\rho}{2}D$ from coupling haplotypes $\{1, 4\}$ to repulsion haplotypes $\{2, 3\}$. For the covariance, row $i$ of $\sigma$ has entries $\pm\sqrt{x_ix_j}$ in the columns of pairs containing $i$, so $(\sigma\sigma^{\top})_{ii} = \sum_{j \ne i} x_ix_j = x_i(1 - x_i)$, and rows $i \ne j$ share only the column $\{i, j\}$, where their entries have opposite signs, giving $-x_ix_j$. In the paper this SDE is simulated by Euler–Maruyama inside a particle-marginal Metropolis–Hastings sampler for selection coefficients from ancient-DNA time series.

## Sources

- Z. He, X. Dai, M. Beaumont and F. Yu, "Detecting and Quantifying Natural Selection at Two Linked Loci from Time Series Data of Allele Frequencies with Forward-in-Time Simulations", Genetics 216 (2020), 521–541, Section 2.1 (Eqs. 1–5), <https://doi.org/10.1534/genetics.120.303463> (PMC7536848).
