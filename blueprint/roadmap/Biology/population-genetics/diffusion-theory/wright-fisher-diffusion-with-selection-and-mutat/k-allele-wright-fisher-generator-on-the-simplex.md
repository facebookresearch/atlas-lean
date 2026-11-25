# Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection

For $K \ge 2$ alleles, a mutation rate matrix $Q = (q_{ij})$ ($q_{ij} \ge 0$ for $i \ne j$, rows summing to $0$) and genic selection
coefficients $\sigma_1, \dots, \sigma_K$, the generator of the $K$-allele Wright–Fisher diffusion acts on twice continuously
differentiable functions $f$ on a neighbourhood of the simplex $\Delta_{K-1} = \{x \in [0, 1]^K : \sum_i x_i = 1\}$ by

$$L f(x) = \frac12 \sum_{i,j=1}^K x_i (\delta_{ij} - x_j)\, \partial_i \partial_j f(x) + \sum_{i=1}^K b_i(x)\, \partial_i f(x), \qquad b_i(x) = \sum_{j} x_j q_{ji} + x_i \Bigl(\sigma_i - \sum_j \sigma_j x_j\Bigr),$$

with time in units of the population size in gene copies. On the simplex $\sum_j x_i(\delta_{ij} - x_j) = 0$ and
$\sum_i b_i = 0$, so $Lf$ depends only on derivatives along the simplex, and $b_i(x) = \sum_{j \ne i} x_j q_{ji} \ge 0$ on the face
$x_i = 0$. Parent-independent mutation is the case $q_{ji} = \frac\theta2 \nu_i$ for $j \ne i$, with $\nu$ a probability vector, which gives
$b_i = \frac\theta2 (\nu_i - x_i)$ without selection. For $K = 2$, in the coordinate $x = x_1$, this is the
[two-allele generator](selection-mutation-generator.md) with $\theta_1 = 2q_{21}$, $\theta_2 = 2q_{12}$ and $\alpha = \sigma_1 - \sigma_2$.

## Depends on

- [Generator of the Wright–Fisher diffusion with selection and mutation](selection-mutation-generator.md)

## Sources

- P. A. Jenkins and D. Spanò, "Exact simulation of the Wright–Fisher diffusion", Annals of Applied Probability 27 (2017), 1478–1509, <https://doi.org/10.1214/16-AAP1236>; preprint <https://arxiv.org/abs/1506.06998>, Section 2 (Wright–Fisher diffusions in $d$ dimensions as projections of the parent-independent Fleming–Viot diffusion). The general generator is stated and checked above.
