# Uniqueness and reversibility of the Dirichlet stationary law under parent-independent mutation

On the simplex $\Delta_K = \{x \in [0, 1]^K : \sum_i x_i = 1\}$, $K \ge 2$, let $L$ be the generator of the neutral $K$-allele Wright–Fisher diffusion with parent-independent mutation, $Lf = \frac12\sum_{i,j}x_i(\delta_{ij} - x_j)\partial_i\partial_jf + \frac12\sum_i(\theta_i - \theta x_i)\partial_if$ with all $\theta_i > 0$ and $\theta = \sum_i\theta_i$, and let $\pi = \mathrm{Dirichlet}(\theta_1, \dots, \theta_K)$, which is [stationary for $L$](../wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md). Then:

1. $L$ is symmetric in $L^2(\pi)$ on polynomials, $\int g\,Lf\,d\pi = \int f\,Lg\,d\pi$, so the diffusion started from $\pi$ is reversible;
2. $\pi$ is the unique stationary law of the diffusion on $\Delta_K$.

In the source's parametrization each lineage mutates at rate $\theta/2$ to type $j$ with probability $\pi_j > 0$, so $\theta_j = \theta\pi_j$; the source states the Dirichlet equilibrium (Birkner, Remark 2.2.16) and, for two types, that the $\mathrm{Beta}(\theta_1, \theta_0)$ law is the unique equilibrium (Fact 2.1.1). Sampling from the stationary population is treated in [sampling consistency and exchangeability](sampling-consistency-and-exchangeability.md).

## Depends on

- [The Dirichlet law is stationary for parent-independent mutation](../wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md)

## Proof depends on

- [Dirichlet-process stationary law of the Fleming–Viot process](../../../../Biology/population-genetics/diffusion-theory/fleming-viot-processes/dirichlet-process-stationary-law.md)

## Expansion

1. Reversibility: symmetry of $L$ in $L^2(\pi)$ on polynomials, from the Dirichlet moments or by projecting the reversible Fleming–Viot process onto a partition into $K$ sets.
2. Uniqueness: $L$ maps polynomials of degree at most $m$ to themselves, so the moments of any stationary law solve the triangular system $\int Lx^n\,d\mu = 0$, whose solution is unique given $\mu(\Delta_K) = 1$; polynomials determine laws on the compact simplex.
3. The two-allele case, the [Beta law](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/beta-pdfreal-eq-wright-density.md).

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, Remark 2.2.16, Fact 2.1.1 and Observation 2.1.2.
