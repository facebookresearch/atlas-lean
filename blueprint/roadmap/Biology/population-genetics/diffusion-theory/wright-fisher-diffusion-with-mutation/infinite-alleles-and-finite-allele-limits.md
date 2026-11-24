# Infinite-alleles limits of finite-allele diffusions

Etheridge (lecture notes, Section 6) treats the neutral $K$-allele Wright–Fisher diffusion in which each gene mutates at total rate $u$ to each of the other $K - 1$ types with equal probability; with $N$ genes its stationary law is the symmetric Dirichlet distribution with parameter $\varepsilon = 2Nu/(K - 1)$ (her equation (20)), and the order statistics of the frequencies have the density of her equation (21). Kingman proved that the law of the first $j$ order statistics converges as $K \to \infty$ for every $j$, and the limit is the Poisson–Dirichlet distribution, which describes the ranked frequencies of the infinitely-many-alleles model (same section, with the representation of the Dirichlet law by normalized independent gamma variables).

The expected homozygosity follows from the Dirichlet moments: for the symmetric Dirichlet law with parameter $\varepsilon$ on $K$ types, $E[X_i] = 1/K$ and $\mathrm{Var}[X_i] = (1/K)(1 - 1/K)/(K\varepsilon + 1)$ (Wikipedia, *Dirichlet distribution*), so

$$\sum_{i=1}^KE[X_i^2] = \frac{1 + \varepsilon}{1 + K\varepsilon}.$$

With $\varepsilon = \theta/(K - 1)$ and $\theta = 2Nu$ fixed, $K\varepsilon \to \theta$ and $\varepsilon \to 0$, so the homozygosity tends to $1/(1 + \theta)$, the Kimura–Crow value. These limits connect the finite-allele Dirichlet equilibrium with the stationary Fleming–Viot measure, whose ranked atom masses are Poisson–Dirichlet.

## Depends on

- [Dirichlet stationary law under parent-independent mutation](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/dirichlet-stationary-law-under-parent-independent-mutation.md)
- [Ranked masses of the stationary Fleming–Viot measure](../../../../Biology/population-genetics/diffusion-theory/fleming-viot-processes/ranked-frequencies-are-poisson-dirichlet.md)
- [Kimura–Crow limit](../../../../Biology/population-genetics/infinite-alleles-model-and-homozygosity/tendsto-eq-homozygosity.md)

## Expansion

1. The $K$-allele diffusion with equal mutation to every other type and its symmetric Dirichlet stationary law.
2. The expected homozygosity $(1 + \varepsilon)/(1 + K\varepsilon)$ and its limit $1/(1 + \theta)$.
3. Convergence of the ranked Dirichlet frequencies to the Poisson–Dirichlet law, through the gamma representation.
4. Sampling: Dirichlet–multinomial samples and their limit, the Ewens sampling formula.

## Sources

- A. Etheridge, *Diffusion process models in mathematical genetics*, lecture notes, University of Oxford, Section 6 (equations (18)–(21) and the following discussion).
- Wikipedia, Dirichlet distribution, moments. <https://en.wikipedia.org/wiki/Dirichlet_distribution>
