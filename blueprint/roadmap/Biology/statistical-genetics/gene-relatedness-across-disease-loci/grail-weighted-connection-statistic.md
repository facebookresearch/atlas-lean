# GRAIL weighted connection statistic and its Poisson–gamma null

Let a genome contain $N$ genes ranked, for each gene $g$, by a similarity score to $g$ (in GRAIL, the correlation of averaged inverse-document-frequency-weighted word vectors from abstracts that reference the genes). Let $N_{\mathrm{SEED}}$ disease regions be given, seed region $s$ containing $n_s$ genes. For a candidate gene $g$ in a query region and each seed region $s$ sharing no gene with that query region, let $R_{g,s}$ be the best (smallest) similarity rank to $g$ among the genes of $s$, and define

$$p_{g,s} = 1 - \Big(1 - \frac{R_{g,s}}{N}\Big)^{n_s},$$

which is approximately uniform on $(0,1)$ when the genes of $s$ are unrelated to $g$. Fix a threshold $p_f$ ($0.1$ in GRAIL); region $s$ is connected to $g$ when $p_{g,s} < p_f$, and then carries weight

$$w_{g,s} = -\log\frac{p_{g,s}}{p_f} \ge 0 .$$

The weighted count is $c_g = \sum_{s \text{ connected}} w_{g,s}$. Under the null, the number of connected regions $n_{\mathrm{hit}}$ is approximately Poisson with mean $\mu = N_{\mathrm{SEED}}\,p_f$, and given $n_{\mathrm{hit}} = k$ the weights are independent standard exponentials, so $c_g$ is $\mathrm{Gamma}(k, 1)$. Hence

$$\mathbb P(C \ge c_g) \approx \sum_{k \ge 1} e^{-\mu}\frac{\mu^k}{k!}\; e^{-c_g}\sum_{j=0}^{k-1}\frac{c_g^j}{j!}$$

for $c_g > 0$, using the closed form of the gamma upper tail for integer shape. The p-value of the gene, $p_g$, is this tail probability; a query region with $n_q$ genes receives the p-value $1 - (1 - \min_g p_g)^{n_q}$ of its best gene, which is reported as the region's candidate.

## Expansion

If $R_{g,s}/N$ is the minimum of $n_s$ roughly uniform rank proportions, its distribution function is $1 - (1-x)^{n_s}$, which is why $p_{g,s}$ is a Šidák-type correction making the per-region score uniform regardless of region size. Conditional on $p_{g,s} < p_f$, $p_{g,s}/p_f$ is uniform on $(0,1)$, so $w_{g,s}$ is exponential with mean one; a sum of $k$ independent standard exponentials is gamma with shape $k$, whose upper tail at $c$ is $e^{-c}\sum_{j<k} c^j/j!$. Mixing over the Poisson number of connections gives the null tail, which weights strong connections more than a simple count would. Raychaudhuri et al. recommend calibrating with simulated random region sets; in such simulations the region p-values are approximately uniform. On 19 validated lipid loci, 13 of the 14 regions with a known lipid-metabolism gene obtained $p < 0.01$, and on Crohn's disease meta-analysis loci higher GRAIL scores predicted replication.

## Sources

- S. Raychaudhuri, R. M. Plenge, E. J. Rossin, A. C. Y. Ng, International Schizophrenia Consortium, S. M. Purcell, et al., "Identifying relationships among genomic disease regions: predicting genes at pathogenic SNP associations and rare deletions", PLoS Genetics 5 (2009), e1000534, <https://doi.org/10.1371/journal.pgen.1000534> (PMC2694358), Methods "Scoring regions for functional relatedness" (Steps 1–4) and "Assessing gene relatedness with text-based similarity".
