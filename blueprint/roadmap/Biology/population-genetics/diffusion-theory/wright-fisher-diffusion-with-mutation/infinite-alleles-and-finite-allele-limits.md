# Infinite-alleles limits of finite-allele diffusions

Consider the neutral $K$-allele Wright–Fisher diffusion in which each gene mutates at total rate $u$ to each of the other $K - 1$ types, $K \ge 2$, with equal probability; with $N$ genes its stationary law is the symmetric Dirichlet distribution with parameter $\varepsilon = 2Nu/(K - 1)$ (Wright 1949). Kingman (1975) proved that if $K \to \infty$ with $K\varepsilon \to \theta$, the law of the first $j$ order statistics of the frequencies converges for every $j$, and the limit is the Poisson–Dirichlet distribution with parameter $\theta$, which describes the ranked frequencies of the infinitely-many-alleles model (Kingman 1975, using the representation of the Dirichlet law by normalized independent gamma variables; Watterson 1976; Ethier and Kurtz 1981, where the limit theorem is obtained as a corollary of the convergence of the diffusions).

The expected homozygosity follows from the Dirichlet moments: for the symmetric Dirichlet law with parameter $\varepsilon$ on $K$ types, $E[X_i] = 1/K$ and $\mathrm{Var}[X_i] = (1/K)(1 - 1/K)/(K\varepsilon + 1)$ (Kotz, Balakrishnan and Johnson 2000, Chapter 49), so

$$\sum_{i=1}^KE[X_i^2] = \frac{1 + \varepsilon}{1 + K\varepsilon}.$$

With $\varepsilon = \theta/(K - 1)$ and $\theta = 2Nu$ fixed, $K\varepsilon \to \theta$ and $\varepsilon \to 0$, so the homozygosity tends to $1/(1 + \theta)$, the Kimura–Crow value (Kimura and Crow 1964). These limits connect the finite-allele Dirichlet equilibrium with the stationary Fleming–Viot measure, whose ranked atom masses are Poisson–Dirichlet.

## Depends on

- [Uniqueness and reversibility of the Dirichlet stationary law under parent-independent mutation](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/dirichlet-stationary-law-under-parent-independent-mutation.md)
- [Ranked masses of the stationary Fleming–Viot measure](../../../../Biology/population-genetics/diffusion-theory/fleming-viot-processes/ranked-frequencies-are-poisson-dirichlet.md)
- [Kimura–Crow limit](../../../../Biology/population-genetics/infinite-alleles-model-and-homozygosity/tendsto-eq-homozygosity.md)

## Expansion

1. The $K$-allele diffusion with equal mutation to every other type and its symmetric Dirichlet stationary law.
2. The expected homozygosity $(1 + \varepsilon)/(1 + K\varepsilon)$ and its limit $1/(1 + \theta)$.
3. Convergence of the ranked Dirichlet frequencies to the Poisson–Dirichlet law, through the gamma representation.
4. Sampling: Dirichlet–multinomial samples and their limit, the Ewens sampling formula.

## Sources

- J. F. C. Kingman, Random discrete distributions, J. R. Stat. Soc. Ser. B 37 (1975), 1–22.
- G. A. Watterson, The stationary distribution of the infinitely-many neutral alleles diffusion model, J. Appl. Probab. 13 (1976), 639–651.
- S. N. Ethier and T. G. Kurtz, The infinitely-many-neutral-alleles diffusion model, Adv. Appl. Probab. 13 (1981), 429–452.
- S. Wright, Adaptation and selection, in *Genetics, Paleontology and Evolution* (G. L. Jepsen, E. Mayr and G. G. Simpson, eds.), Princeton University Press (1949), 365–389.
- S. Kotz, N. Balakrishnan and N. L. Johnson, *Continuous Multivariate Distributions, Vol. 1: Models and Applications*, 2nd ed., Wiley (2000), Chapter 49.
- M. Kimura and J. F. Crow, The number of alleles that can be maintained in a finite population, Genetics 49 (1964), 725–738. <https://doi.org/10.1093/genetics/49.4.725>
