# Sampling ensembles of binary co-purification data from spectral counts

Let $(n_{ij})$ be an AP-MS matrix of spectral counts, rows indexing prey proteins and columns indexing purification experiments, and fix $p \in (0, 1)$, the probability that a single spectral count reflects a true observation. If the $n_{ij}$ counts are viewed as independent observations, the probability that the bait–prey observation in cell $(i, j)$ is not an artifact is

$$q_{ij} = 1 - (1 - p)^{n_{ij}},$$

which is $0$ for $n_{ij} = 0$ and increases to $1$ as $n_{ij} \to \infty$. The **sampling framework** draws $T$ independent binary matrices $B^{(1)}, \dots, B^{(T)}$ with independent entries $B^{(t)}_{ij} \sim \mathrm{Bernoulli}(q_{ij})$, applies any interaction score $S$ that operates on binary data to each realization, and reports the ensemble score

$$\bar S_{AB} = \frac{1}{T} \sum_{t=1}^{T} S_{AB}\big(B^{(t)}\big)$$

for every protein pair $(A, B)$, which converges almost surely to $\mathbb{E}[S_{AB}(B)]$ as $T \to \infty$.

A standard binary score that can be plugged in is the co-purification null model of Hart et al.: with $X_{AB}$ the number of experiments in which $A$ and $B$ co-purify, $N_A$ and $N_B$ the numbers of co-purifying pairs involving $A$ and $B$, and $N$ the total number of co-purifying pairs, the score is

$$S_{AB} = -\log\big(1 - F_{\mathrm{Pois}}(X_{AB}; \lambda_{AB})\big), \qquad \lambda_{AB} = \frac{N_A}{N}\cdot\frac{N_B}{N}\cdot N,$$

the Poisson approximation, for large studies, of a hypergeometric tail under random choice of partners in proportion to their observed number of interactions.

## Depends on

- [Poisson distribution function as a function of the mean](../../../../Probability/distributions/continuous/poisson-gamma-duality/poisson-gamma-duality-identity/poisson-cdf.md)

## Remarks

The probability $q_{ij}$ is the chance that at least one of $n_{ij}$ independent spectra, each genuine with probability $p$, is genuine, so low-count observations (counts of $1$ or $2$ make up nearly half of the positive entries in a large Drosophila data set) are often dropped in a realization while high-count observations are almost always kept. Because each realization has the same format as the binary input of an existing method, the method is used without modification, and the ensemble mean averages over the uncertainty of low-count observations; scores with unbounded negative values are truncated at $0$ before averaging. The null intensity $\lambda_{AB} = N_A N_B / N$ is a rank-one matrix, so the Hart score, and related scores such as HGSCore and SAINT, can be read as decomposing observations into a rank-one background plus sparse true interactions. In benchmarks, about $120$ realizations sufficed for stable rankings.

## Sources

- G. Tucker, P.-R. Loh and B. Berger, "A sampling framework for incorporating quantitative mass spectrometry data in protein interaction analysis", *BMC Bioinformatics* 14 (2013), 299, section "Sampling framework" and Discussion, <https://doi.org/10.1186/1471-2105-14-299> (PMC3851523).
