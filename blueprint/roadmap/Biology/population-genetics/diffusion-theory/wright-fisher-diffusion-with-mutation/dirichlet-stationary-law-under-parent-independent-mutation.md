# Uniqueness of the Dirichlet stationary law under parent-independent mutation

On the simplex $\Delta_K = \{x \in [0, 1]^K : \sum_i x_i = 1\}$, $K \ge 2$, let $L$ be the generator of the neutral $K$-allele Wright–Fisher diffusion with parent-independent mutation, $Lf = \frac12\sum_{i,j}x_i(\delta_{ij} - x_j)\partial_i\partial_jf + \frac12\sum_i(\theta_i - \theta x_i)\partial_if$ with all $\theta_i > 0$ and $\theta = \sum_i\theta_i$, and let $\pi = \mathrm{Dirichlet}(\theta_1, \dots, \theta_K)$, which is [stationary for $L$](../wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md). Then $\pi$ is the unique stationary law of the diffusion on $\Delta_K$.

Reversibility of the diffusion started from $\pi$ is the one-locus case without selection of the reversibility proposition in [exact filtering and smoothing of coupled Wright–Fisher diffusions by duality](../transition-densities-of-wright-fisher-diffusions/filtering-fleming-viot-population-frequencies/exact-filtering-and-smoothing-of-coupled-wright-fisher-diffusions.md) and is not restated here. With each lineage mutating at rate $\theta/2$ to type $j$ with probability $\pi_j > 0$, $\theta_j = \theta\pi_j$. The Dirichlet equilibrium is Wright's (1949), and for two types the Beta law (Wright 1931). For a finite type space this diffusion is the Fleming–Viot process with parent-independent (uniform) mutation, whose stationary law Ethier and Kurtz (1993) show to be unique and reversible; Li, Shiga and Yao (1999) prove the converse, that for irreducible mutation reversibility forces the mutation to be parent-independent. Sampling from the stationary population is treated in [sampling consistency and exchangeability](sampling-consistency-and-exchangeability.md).

## Depends on

- [The Dirichlet law is stationary for parent-independent mutation](../wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md)
- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)

## Proof depends on

- [Dirichlet-process stationary law of the Fleming–Viot process](../../../../Biology/population-genetics/diffusion-theory/fleming-viot-processes/dirichlet-process-stationary-law.md)

## Expansion

1. Uniqueness: $L$ maps polynomials of degree at most $m$ to themselves, so the moments of any stationary law solve the triangular system $\int Lx^n\,d\mu = 0$, whose solution is unique given $\mu(\Delta_K) = 1$; polynomials determine laws on the compact simplex.
2. The two-allele case, the [Beta law](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/beta-pdfreal-eq-wright-density.md).

## Sources

- S. Wright, Adaptation and selection, in *Genetics, Paleontology and Evolution* (G. L. Jepsen, E. Mayr and G. G. Simpson, eds.), Princeton University Press (1949), 365–389.
- S. Wright, Evolution in Mendelian populations, Genetics 16 (1931), 97–159. <https://doi.org/10.1093/genetics/16.2.97>
- S. N. Ethier and T. G. Kurtz, Fleming–Viot processes in population genetics, SIAM J. Control Optim. 31 (1993), 345–386. <https://doi.org/10.1137/0331019>
- Z. Li, T. Shiga and L. Yao, A reversibility problem for Fleming–Viot processes, Electron. Commun. Probab. 4 (1999), 65–76.
- O. Papaspiliopoulos, M. Ruggiero and D. Spanò, Conjugacy properties of time-evolving Dirichlet and gamma random measures, Electron. J. Stat. 10 (2016), 3452–3489, Section 2.1.2, eqs. (7), (10), (11) (the uniqueness clause). <https://doi.org/10.1214/16-EJS1194>
