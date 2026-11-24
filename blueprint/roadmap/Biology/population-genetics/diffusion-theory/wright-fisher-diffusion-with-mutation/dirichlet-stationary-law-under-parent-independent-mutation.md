# Dirichlet stationary law under parent-independent mutation

On the simplex $\Delta_K = \{x \in [0, 1]^K : \sum_i x_i = 1\}$ the $K$-allele Wright–Fisher diffusion has generator $Lf = \frac12\sum_{i,j}x_i(\delta_{ij} - x_j)\partial_i\partial_jf + \sum_ib_i(x)\partial_if$, with drift $b$ from mutation and selection. Under parent-independent mutation with $b_i(x) = \frac12(\theta_i - \theta x_i)$, $\theta = \sum_i\theta_i$, and all $\theta_i > 0$, the equilibrium type distribution is the Dirichlet law $\pi(dx) \propto \prod_ix_i^{\theta_i - 1}\,dx$ on $\Delta_K$, that is $\mathrm{Dirichlet}(\theta_1, \dots, \theta_K)$; in the source's parametrization each lineage mutates at rate $\theta/2$ to type $j$ with probability $\pi_j > 0$, so $\theta_j = \theta\pi_j$ (Birkner, Remark 2.2.16; for two types the $\mathrm{Beta}(\theta_1, \theta_0)$ law is the unique equilibrium, Fact 2.1.1). Its moments are $E_\pi[x_i] = \theta_i/\theta$ and $E_\pi[x_ix_j] = \theta_i(\theta_j + \delta_{ij})/(\theta(\theta + 1))$, and a sample of $n$ genes from the stationary population has the Dirichlet-multinomial law (for two types the Beta-binomial law, Birkner, Observation 2.1.2). Stationarity and reversibility of this Dirichlet law for the $K$-allele diffusion follow by projecting the [Dirichlet-process stationary law of the Fleming–Viot process](../../../../Biology/population-genetics/diffusion-theory/fleming-viot-processes/dirichlet-process-stationary-law.md) onto a partition into $K$ sets. The target is what that page leaves open: the moments, the Dirichlet-multinomial sampling law, and uniqueness of the stationary law for $K \ge 3$.

## Depends on

- [Dirichlet-process stationary law of the Fleming–Viot process](../../../../Biology/population-genetics/diffusion-theory/fleming-viot-processes/dirichlet-process-stationary-law.md)

## Expansion

1. The zero-flux condition $\frac12\sum_j\partial_j(a_{ij}\pi) = b_i\pi$ for the Dirichlet density.
2. Reversibility: symmetry of $L$ in $L^2(\pi)$ on polynomials.
3. Uniqueness of the stationary law (from irreducibility and the polynomial moment system).
4. Moments and the Dirichlet-multinomial sampling law; the two-allele case, the Beta law ([Beta density as Wright's stationary density](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/beta-pdfreal-eq-wright-density.md)).

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, Remark 2.2.16, Fact 2.1.1 and Observation 2.1.2.
