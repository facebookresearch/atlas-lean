# Point-process likelihood dominates binned likelihoods

Let a snapshot $\vec x = \{x_1, \dots, x_n\}$ be a Poisson point process on $\Omega$ with intensity $u(x;\theta)$, for example the birth–diffusion–death intensity with $\theta = (\lambda, \mu)$. The point-process likelihood is

$$ L(\theta;\vec x) = \Big(\prod_{i=1}^{n} u(x_i;\theta)\Big)\, \exp\Big(-\int_\Omega u(x;\theta)\, dx\Big) . $$

**Limit of binned posteriors.** If $\mathcal{A}_K$ is a nested sequence of partitions of $\Omega$ whose mesh tends to zero, and $\pi_K(\theta\mid\vec x)$ is the posterior under prior $\pi$ given only the bin counts, then $\pi_K(\theta \mid \vec x) \to L(\theta;\vec x)\pi(\theta)/\int_\Theta L(\vartheta;\vec x)\pi(\vartheta)\,d\vartheta$.

**Fisher information.** By Campbell's formula $\mathbb{E}\sum_i g(x_i) = \int_\Omega g\,u$, the information matrix of the point-process likelihood is

$$ I_{ij}(\theta) = \int_\Omega \frac{\partial_{\theta_i} u(x;\theta)\, \partial_{\theta_j} u(x;\theta)}{u(x;\theta)}\, dx . $$

**Binning loses information.** For any partition $\{A_j\}$ of $\Omega$ and a scalar parameter $\theta$, the information of the binned Poisson counts satisfies

$$ I_{\mathrm{bin}}(\theta) = \sum_j \frac{\big(\int_{A_j} \partial_\theta u\, dx\big)^2}{\int_{A_j} u\, dx} \le \int_\Omega \frac{(\partial_\theta u)^2}{u}\, dx = I_{\mathrm{unbin}}(\theta) . $$

## Depends on

- [Poisson snapshot theorem for birth–diffusion–death particles](poisson-snapshot-theorem-for-birth-diffusion-death-particles.md)

## Expansion

Once the partition is fine enough that each bin holds at most one particle, the binned probability equals $e^{-\int_\Omega u}\prod_i \int_{A_{k_i}} u$; dividing by the bin volumes and applying the Lebesgue differentiation theorem gives $L(\theta;\vec x)$, and the volume factors cancel in the posterior. The information inequality is, bin by bin, the Cauchy–Schwarz inequality $\big(\int_A \partial_\theta u\big)^2 = \big(\int_A (\partial_\theta u/\sqrt u)\sqrt u\big)^2 \le \int_A (\partial_\theta u)^2/u \cdot \int_A u$. Since $u > 0$ when $\lambda > 0$, the diagonal entries are positive; D-optimal designs maximize $\det I$, and cell-to-cell geometric heterogeneity can increase it for some parameter regimes.

## Sources

- Christopher E. Miles, Scott A. McKinley, Fangyuan Ding, Richard B. Lehoucq, "Inferring Stochastic Rates from Heterogeneous Snapshots of Particle Positions", Bulletin of Mathematical Biology 86 (2024), 74, <https://doi.org/10.1007/s11538-024-01301-4>. Published version of arXiv:2311.04880, cited next; locators there refer to the arXiv version.
- C. E. Miles, S. A. McKinley, F. Ding, R. B. Lehoucq, "Inferring stochastic rates from heterogeneous snapshots of particle positions", arXiv:2311.04880 (2023), Section 2.3 (Definition 2.3), Section 3.1 (Theorem 3.1, Campbell–Hardy formula, and the information matrix), Section 3.3 (heterogeneity), and Section 4.3 (Proposition 4.1) and Section 4.4 (Proposition 4.3). <https://doi.org/10.48550/arXiv.2311.04880>
