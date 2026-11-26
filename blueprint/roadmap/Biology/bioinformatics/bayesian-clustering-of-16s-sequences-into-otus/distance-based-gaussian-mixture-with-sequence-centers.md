# Distance-based Gaussian mixture with sequence centers

Let $x_1, \dots, x_N$ be marker-gene sequences with pairwise dissimilarities $D(x_i, x_j)$ (in percent, from banded pairwise alignment). The CROP model treats them as independent draws from a mixture with an unknown number $k$ of clusters,

$$p(x_i \mid k, \pi, \mu, \sigma^2) = \sum_{j=1}^{k} \pi_j f(x_i; \mu_j, \sigma_j^2), \qquad f(x_i; \mu_j, \sigma_j^2) = \frac{1}{\sqrt{2\pi \sigma_j^2}} \exp\Bigl(-\frac{D^2(x_i, \mu_j)}{2\sigma_j^2}\Bigr),$$

where each center $\mu_j$ is itself one of the observed sequences, chosen without replacement, $\pi = (\pi_1, \dots, \pi_k)$ are mixture weights, and latent labels $Z_i$ with $\Pr(Z_i = j) = \pi_j$ give $p(x_i \mid Z_i = j) = f(x_i; \mu_j, \sigma_j^2)$. The priors are $\pi \mid k \sim \mathrm{Dirichlet}(\gamma, \dots, \gamma)$, $\sigma_j^2 \sim \text{Inverse-Gamma}(\alpha, \beta)$ restricted to $[L, U]$, and a Poisson prior on $k$. The posterior over $(k, \pi, \mu, \sigma^2)$ is explored by a birth–death Markov chain Monte Carlo sampler in which births propose as new centers sequences far from their current centers, and the maximum-posterior state after burn-in defines the operational taxonomic units (OTUs). The variance bounds encode the OTU resolution: $[L, U] = [1, 2.25]$ (so $\sigma_j \in [1, 1.5]$) corresponds to clustering at about $3\%$ dissimilarity, and $[2.25, 6.25]$ ($\sigma_j \in [1.5, 2.5]$) to about $5\%$.

## Expansion

Replacing a Euclidean mean by a medoid-like center sequence lets a Gaussian likelihood act on alignment distances, which have no vector-space mean; the spread $\sigma_j$ then absorbs both sequencing errors and true within-OTU variation, so OTUs need not be separated by a hard threshold. About $95\%$ of a Gaussian's mass lies within $2\sigma$ of its center, so capping $\sigma$ at $1.5$ keeps most members of a cluster within about $3\%$ of its center, which is how the variance bounds translate into the conventional species-level threshold. The birth–death sampler varies $k$ without a fixed number of clusters, unlike hierarchical clustering whose result depends on the linkage rule and cutoff. For speed, densities with $D \ge 15\%$ are set to zero, clusters are processed in blocks of 100–1000 sequences, and centers are updated only when a birth occurs.

## Sources

- Hao X, Jiang R, Chen T. Clustering 16S rRNA for OTU prediction: a method of unsupervised Bayesian clustering. *Bioinformatics* 27:611–618 (2011), Methods, "Gaussian mixture model", "The birth–death process" and "Prior setting". DOI <https://doi.org/10.1093/bioinformatics/btq725>. PMCID PMC3042185.
- Stephens M. Bayesian analysis of mixture models with an unknown number of components: an alternative to reversible jump methods. *Annals of Statistics* 28:40–74 (2000). DOI <https://doi.org/10.1214/aos/1016120364>.
