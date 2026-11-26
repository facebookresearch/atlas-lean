# Integrating out population-size parameters with inverse-gamma priors

**Setting.** Under the multispecies coalescent, fix a species tree with divergence times and consider one branch (population) $b$ with mutation-scaled size parameter $\theta_b = 4N_b\mu$, time measured in expected mutations per site. Each pair of lineages in population $b$ coalesces at rate $2/\theta_b$. For a gene tree at one locus, let $m_b$ be the number of coalescent events inside population $b$ and, for each interval of length $t$ during which $j$ lineages are present in $b$ (including the last interval up to the top of the population), accumulate

$$T_b = \sum_{\text{intervals in } b} j(j-1)\, t .$$

Then the density of the coalescent history of the gene tree inside $b$ is

$$f_b(G \mid \theta_b) = \left(\frac{2}{\theta_b}\right)^{m_b} \exp\!\left(-\frac{T_b}{\theta_b}\right),$$

and the gene-tree density given the species tree is the product of $f_b$ over populations and loci (with $m_b$ and $T_b$ summed over loci).

**Proposition.** If $\theta_b \sim \mathrm{IG}(\alpha, \beta)$ a priori, with density $\beta^\alpha \theta^{-\alpha-1} e^{-\beta/\theta}/\Gamma(\alpha)$, then

$$\int_0^\infty f_b(G \mid \theta_b)\, \pi(\theta_b)\, d\theta_b = \frac{2^{m_b}\, \beta^{\alpha}\, \Gamma(\alpha + m_b)}{\Gamma(\alpha)\, (\beta + T_b)^{\alpha + m_b}},$$

and the posterior is again inverse-gamma: $\theta_b \mid G \sim \mathrm{IG}(\alpha + m_b,\ \beta + T_b)$.

## Expansion

While $j$ lineages are present, the waiting time to the next coalescence is exponential with rate $\binom{j}{2}\frac{2}{\theta_b} = j(j-1)/\theta_b$, and each coalescent event contributes the rate $2/\theta_b$ of the specific pair that merges; lineages that reach the top of the population without coalescing contribute only the survival factor. Multiplying over intervals gives $f_b$. The integrand $\theta^{-(\alpha + m_b) - 1} e^{-(\beta + T_b)/\theta}$ is an unnormalized inverse-gamma density, which yields the closed form. In Bayesian species-tree software this conjugacy lets the $\theta$ parameters be removed analytically from the Markov chain state; the chain then moves only over species trees, divergence times and gene trees, which improves the mixing of trans-model moves between species-tree topologies. The inverse-gamma prior $\mathrm{IG}(\alpha, \beta)$ has mean $\beta/(\alpha - 1)$ for $\alpha > 1$ and variance $\beta^2/[(\alpha-1)^2(\alpha-2)]$ for $\alpha > 2$; $\alpha = 3$ is a common diffuse choice.

## Sources

- Flouri T, Jiao X, Rannala B, Yang Z, "Species Tree Inference with BPP Using Genomic Sequences and the Multispecies Coalescent" (2018), sections "Species Tree Inference Using BPP" and "The Control File" (analytic integration of the $\theta$ parameters under conjugate inverse-gamma priors, after Hey and Nielsen 2007), <https://doi.org/10.1093/molbev/msy147>, PMCID PMC6188564.
- B. Rannala and Z. Yang, "Bayes estimation of species divergence times and ancestral population sizes using DNA sequences from multiple loci", Genetics 164 (2003) 1645–1656, <https://doi.org/10.1093/genetics/164.4.1645>.
- J. Hey and R. Nielsen, "Integration within the Felsenstein equation for improved Markov chain Monte Carlo methods in population genetics", Proceedings of the National Academy of Sciences USA 104 (2007) 2785–2790, <https://doi.org/10.1073/pnas.0611164104>.
