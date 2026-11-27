# Subgenome diffusion for a polyploid with homoeologous exchange

Consider one population of a $K$-ploid organism whose genome consists of $S$ subgenomes of ploidies $k_1,\dots,k_S$, with $\sum_ik_i=K$. Let $N$ be a reference number of individuals and $\nu(t)>0$ the relative population size. Let $x_i$ be the frequency of a derived allele (infinite sites) among the $N\nu k_i$ chromosomes of subgenome $i$, and $e_{i\leftrightarrow j}$ the per-meiosis probability that genetic material is exchanged between subgenomes $i$ and $j$ (homoeologous crossover or non-disomic inheritance).

**Per-generation moments.** Under Wright-Fisher resampling within each subgenome, the next-generation carrier count in subgenome $i$ is binomial with $N\nu k_i$ trials and success probability $x_i$. So

$$\operatorname{Var}(\Delta x_i)=\frac{x_i(1-x_i)}{N\nu k_i},\qquad \operatorname{Cov}(\Delta x_i,\Delta x_j)=0\quad(i\ne j),$$

while exchange moves the mean frequency of subgenome $i$ toward that of subgenome $j$ by $e_{i\leftrightarrow j}(x_j-x_i)/k_i$ per generation.

**Diffusion equation.** Measuring time $t$ in units of $2N$ generations and setting $E_{i\leftrightarrow j}=Ne_{i\leftrightarrow j}$, so that the rescaled exchange drift $2N\,e_{i\leftrightarrow j}/k_i$ equals $(2/k_i)E_{i\leftrightarrow j}$, the density $\phi(x_1,\dots,x_S,t)$ of derived mutations satisfies

$$\frac{\partial\phi}{\partial t}=\sum_{i=1}^S\frac12\cdot\frac2{k_i}\,\frac{\partial^2}{\partial x_i^2}\left[\frac{x_i(1-x_i)}{\nu(t)}\phi\right]-\sum_{i=1}^S\frac2{k_i}\,\frac{\partial}{\partial x_i}\left[\sum_{j\ne i}E_{i\leftrightarrow j}(x_j-x_i)\,\phi\right].$$

This is the [multi-population diffusion with migration](../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md), rescaled subgenome by subgenome:

- **Drift** in subgenome $i$ is multiplied by $2/k_i$ relative to a diploid population, so a tetraploid subgenome ($k_i=4$) drifts at half the diploid rate. Mutation influx into subgenome $i$ carries the same factor.
- **Exchange** acts like symmetric migration, but its effect on subgenome $i$ carries the factor $2/k_i$. A symmetric exchange between subgenomes of unequal ploidy therefore changes allele frequencies asymmetrically. For $k_i=2$ the per-generation fraction of exchanged chromosomes is $m=e_{i\leftrightarrow j}/2$, the diploid scaled migration rate is $M=2Nm=Ne_{i\leftrightarrow j}=E_{i\leftrightarrow j}$, and the term is the diploid migration term with $M=E_{i\leftrightarrow j}$.
- $E_{i\leftrightarrow j}=0$ gives a disomic **allopolyploid**: independent subgenome diffusions that share only the demography $\nu(t)$. Intermediate $E$ gives a **segmental allopolyploid**. Very large $E$ mixes the subgenomes into an effectively single pool, as in a tetrasomic **autopolyploid** (compare [autotetraploid segregation](../hardy-weinberg-law/autopolyploid-segregation.md)).

## Depends on

- [Multi-population diffusion for the joint allele-frequency density](../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md)

## Proof depends on

Its proof is the diffusion limit of the per-generation moments above, as the Expansion describes.

## Expansion

The variance follows from dividing a $\mathrm{Binomial}(N\nu k_i,x_i)$ carrier count by $N\nu k_i$. Sampling is independent across subgenomes, so all cross-diffusion terms $W_{ij}$ in the general Kimura forward equation

$$\partial_\tau\phi=\tfrac12\sum_i\partial_{x_i}^2(V_i\phi)+\sum_{i}\sum_{j\ne i}\partial_{x_i}\partial_{x_j}(W_{ij}\phi)-\sum_i\partial_{x_i}(M_i\phi)$$

vanish. Multiplying the per-generation moments by $2N$ converts generations to the diploid time unit: the drift variance becomes $2x_i(1-x_i)/(\nu k_i)$ and the exchange drift $2Ne_{i\leftrightarrow j}(x_j-x_i)/k_i=(2/k_i)E_{i\leftrightarrow j}(x_j-x_i)$ with $E_{i\leftrightarrow j}=Ne_{i\leftrightarrow j}$. Blischak et al. print Eq. (2) with the coefficient $2E_{i\leftrightarrow j}/k_i$ but write $E_{i\leftrightarrow j}=2Ne_{i\leftrightarrow j}$; with the per-generation coefficient $e_{i\leftrightarrow j}/k_i$ derived just before Eq. (2), that definition would give $E_{i\leftrightarrow j}/k_i$ instead. This page keeps the printed form of the equation and the per-generation derivation, and so scales the exchange rate as $E_{i\leftrightarrow j}=Ne_{i\leftrightarrow j}$, which also gives the diploid check above. The equation is solved numerically together with the binomial sampling formula for the [subgenome frequency spectrum](collapsed-polyploid-site-frequency-spectrum.md), and the two together give the expected data for likelihood-based inference of bottleneck size, formation time and exchange rate. The [expected site frequency spectrum](../diffusion-theory/poisson-random-field-model/expected-sfs.md) is the one-population, diploid analogue of that sampling formula. Exchange of single chromosomes is modelled here, not of chromosome pairs.

## Sources

- P. D. Blischak, M. Sajan, M. S. Barker and R. N. Gutenkunst, "Demographic history inference and the polyploid continuum", Genetics 224(4) (2023), iyad107, <https://doi.org/10.1093/genetics/iyad107>, PMCID PMC10411560. Section "A diffusion approximation for polyploids", Equations (1) and (2), and the subsequent discussion of the $2/k_i$ factors; Fig. 1 for the polyploid continuum.
