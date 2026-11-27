# Fleming–Viot diffusion with parent-independent mutation

Let $E$ be a compact metric space, $\nu_0$ a probability measure on $E$ and $\theta > 0$. The Fleming–Viot process with parent-independent mutation at total rate $\theta/2$ to $\nu_0$ is the solution of the [Fleming–Viot martingale problem](fleming-viot-martingale-problem-solutions-satisf.md) on $\mathcal M_1(E)$ with the bounded mutation operator

$$B f(x) = \frac\theta2 \Bigl(\int_E f\, d\nu_0 - f(x)\Bigr), \qquad f \in C(E),$$

and the resampling part of the Fleming–Viot generator. It is [well-posed on a compact type space](fleming-viot-well-posedness-on-a-compact-type-sp.md). For a partition of $E$ into Borel sets $E_1, \dots, E_K$, the vector of masses $(\mu(E_1), \dots, \mu(E_K))$ is the [$K$-allele Wright–Fisher diffusion](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md) with parent-independent mutation, drift $\frac\theta2(\nu_i - z_i)$ with $\nu_i = \nu_0(E_i)$, and resampling coefficients $z_i(\delta_{ij} - z_j)$; for finite $E$ this is the [finite-type correspondence](finite-type-fleming-viot-k-allele-wright-fisher.md).

## Depends on

- [Finite-type Fleming–Viot and Wright–Fisher martingale problems](finite-type-fleming-viot-k-allele-wright-fisher.md)
- [Fleming-Viot well-posedness on a compact type space](fleming-viot-well-posedness-on-a-compact-type-sp.md)
- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)
- [Fleming–Viot martingale-problem solutions satisfy the moment hierarchy](fleming-viot-martingale-problem-solutions-satisf.md)

## Expansion

A full proof page must still establish:

- that finite-partition projections are $K$-allele diffusions with $\nu_i = \nu_0(E_i)$, by the aggregation argument for parent-independent mutation;
- that the units of $\theta$ and of time agree with those of the $K$-allele Wright–Fisher pages;
- the extension of the martingale problem from continuous test functions to bounded Borel test functions by bounded pointwise approximation, which makes $z_i = \mu(E_i)$ admissible for every Borel partition.

## Sources

- S. N. Ethier and T. G. Kurtz, "The infinitely-many-neutral-alleles diffusion model", *Advances in Applied Probability* 13(3):429–452, 1981, <https://doi.org/10.2307/1426779>
- S. N. Ethier and T. G. Kurtz, "Fleming–Viot processes in population genetics", *SIAM Journal on Control and Optimization* 31(2):345–386, 1993, <https://doi.org/10.1137/0331019>
- S. N. Ethier and R. C. Griffiths, "The transition function of a Fleming–Viot process", *Annals of Probability* 21(3):1571–1590, 1993, <https://doi.org/10.1214/aop/1176989131>
