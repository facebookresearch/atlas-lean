# Binomial mixture genotype model with MAP-EM parameter fitting

At a genomic position $i$ with $N_i$ aligned reads, let $a_i$ be the number of reads matching the reference allele, and let the genotype $G_i \in \{aa, ab, bb\}$ (homozygous reference, heterozygous, homozygous non-reference) have prior $\Pr(G_i = k) = \pi_k$. SNVMix1 assumes

$$p(a_i \mid G_i = k, N_i, \mu) = \mathrm{Binom}(a_i \mid \mu_k, N_i),$$

with $\mu_k$ the probability that a read from genotype $k$ shows the reference allele (expected near $1$, $0.5$ and $0$). The genotype posterior is

$$\gamma_i(k) = \frac{\pi_k \mathrm{Binom}(a_i \mid \mu_k, N_i)}{\sum_{j} \pi_j \mathrm{Binom}(a_i \mid \mu_j, N_i)} .$$

With conjugate priors $\pi \sim \mathrm{Dirichlet}(\delta)$ and $\mu_k \sim \mathrm{Beta}(\alpha_k, \beta_k)$, maximum a posteriori EM over $T$ training positions alternates genotype assignment with the updates

$$\pi_k^{\mathrm{new}} = \frac{\sum_{i=1}^{T} I(G_i = k) + \delta_k}{\sum_j \bigl(\sum_{i=1}^{T} I(G_i = j) + \delta_j\bigr)}, \qquad \mu_k^{\mathrm{new}} = \frac{\sum_{i} I(G_i = k)\, a_i + \alpha_k - 1}{\sum_{i} I(G_i = k)\, N_i + \alpha_k + \beta_k - 2},$$

until the complete-data log-posterior stops increasing. A position is called a variant when $\gamma_i(ab) + \gamma_i(bb)$ is large.

## Expansion

The binomial components are well separated when $N_i$ is moderate, so the posterior concentrates on one genotype and the method needs no hard depth threshold; low-depth positions simply get flatter posteriors. Learning $\mu_k$ from the data instead of fixing it to $1$, $0.5$, $0$ absorbs systematic reference bias and, in tumours, the shift of heterozygous allele fractions caused by normal-cell admixture and copy-number change, and fitting the parameters gave better accuracy than fixed-parameter calling. The strong default priors ($\alpha = (1000, 500, 1)$, $\beta = (1, 500, 1000)$, $\delta = (1000, 100, 100)$) keep the components anchored to their biological meaning and encode that most positions are homozygous reference. Hard read-depth thresholds, by contrast, were shown to reduce sensitivity.

## Sources

- Goya R, Sun MG, Morin RD, Leung G, Ha G, Wiegand KC, et al. SNVMix: predicting single nucleotide variants from next-generation sequencing of tumors. *Bioinformatics* (2010), Methods, "SNVMix model specification", "Prior distributions", "Model fitting and parameter estimation" and "Modeling base and mapping qualities", equations (1)–(8). DOI <https://doi.org/10.1093/bioinformatics/btq040>. PMCID PMC2832826.
