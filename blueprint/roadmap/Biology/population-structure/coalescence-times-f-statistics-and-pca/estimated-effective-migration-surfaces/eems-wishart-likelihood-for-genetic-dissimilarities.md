# EEMS Wishart likelihood for genetic dissimilarities

**Data.** For $n$ individuals genotyped at $p$ biallelic SNPs, $Z_{il} \in \{0,1,2\}$, let

$$D_{ij} = \frac{1}{p}\sum_{l=1}^{p} (Z_{il} - Z_{jl})^2$$

be the observed dissimilarity matrix. Let $L$ be the $(n-1)\times n$ contrast matrix with rows $L_i = e_i - e_{i+1}$ and set $W = -LDL^\top$. Then $W = \tfrac{2}{p}(LZ)(LZ)^\top$ (with genotypes centered per locus, which $L$ annihilates), so $W$ is positive semidefinite, and positive definite when the individuals are linearly independent (which requires $p \ge n$); since $L$ is a basis of contrasts, $W$ determines $D$.

**Model.** Individual $i$ is sampled from deme $\delta(i)$ of a stepping-stone graph with migration rates $m$ and diversity rates $q$. As the mutation rate tends to $0$, $\mathbb{E}D_{ij}$ is proportional to the expected coalescence time, so

$$\mathbb{E}\{D \mid m, q, \sigma^2\} = \sigma^2 \Delta(m, q),$$

where $\Delta$ is the hollow symmetric matrix with $\Delta_{ii} = 0$ (matching $D_{ii} = 0$) and, for **distinct** individuals $i \ne j$, including two distinct individuals from the same deme,

$$\Delta_{ij} = 4T_{\delta(i)\delta(j)} - T_{\delta(i)\delta(i)} - T_{\delta(j)\delta(j)}$$

for diploid samples ($\Delta_{ij} = T_{\delta(i)\delta(j)}$ for haploid samples). Here $T_{\alpha\beta}$ is the expected coalescence time of two distinct lineages sampled from demes $\alpha$ and $\beta$, computed or approximated by the [resistance-distance approximation](resistance-distance-approximation-of-expected-coalescence-times.md); for $\delta(i) = \delta(j) = \alpha$ the off-diagonal entry is $2T_{\alpha\alpha}$ (diploid) or $T_{\alpha\alpha}$ (haploid), and the formula is not applied on the diagonal. The likelihood is the Wishart law

$$W \mid k, m, q, \sigma^2 \sim \mathcal{W}_{n-1}\!\left(k,\ -\frac{\sigma^2}{k}\, L\Delta(m, q)L^\top\right),$$

with this hollow $\Delta$ in the scale, mean $\mathbb{E}W = -\sigma^2 L\Delta L^\top$, and the degrees of freedom $k$ a free parameter. For microsatellites, each locus $l$ gets its own rank-one statistic $W^{(l)} = -LD^{(l)}L^\top$, a scale $\sigma_l^2$, and a singular Wishart law $\mathcal{W}_{n-1}(1, -\sigma_l^2 L\Delta L^\top)$, independent across loci.

## Remarks

The dissimilarities are not independent and $D$ itself is not positive definite, but projecting onto contrasts gives a positive-definite matrix that is a scaled sum of outer products of $p$ (correlated) vectors, which the Wishart family models with an effective number of degrees of freedom $k$ standing in for the number of independent loci. Since $L\mathbf{1} = 0$, contrasts remove any constant added to every entry of the matrix (diagonal included), so only differences in coalescence times matter. The factor $4$ in the diploid case comes from averaging the four lineage pairs between two diploid individuals, while each individual's own two lineages contribute the within-deme terms. Combined with the Voronoi prior on $m$, MCMC over $(m, q, \sigma^2, k)$ gives the posterior mean migration surface, plotted on a $\log_{10}$ scale relative to the overall mean.

## Depends on

- [Resistance-distance approximation of expected coalescence times](resistance-distance-approximation-of-expected-coalescence-times.md)

## Sources

- D. Petkova, J. Novembre and M. Stephens, "Visualizing spatial population structure with estimated effective migration surfaces", Nature Genetics 48 (2016), 94–100, Online Methods (Equations (1)–(8); Equations (6)–(8) for distinct individuals), <https://doi.org/10.1038/ng.3464>, PMCID PMC4696895.
