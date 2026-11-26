# Exponential decay of LD among introgressed alleles

Ascertain SNPs at which the archaic genome (Neandertal) carries the derived allele, polarized against an outgroup (chimpanzee), and whose derived allele has frequency below 10% in the target population. For a genetic distance $x$ (in Morgans), let $S(x)$ be the set of ascertained SNP pairs at distance $x$ and define

$$\bar D(x) = \frac{1}{|S(x)|}\sum_{(i,j)\in S(x)} D(i,j),$$

where $D(i,j)$ is the signed linkage disequilibrium computed on the derived alleles; with unphased data, $D(i,j)$ is the covariance of the genotypes at $i$ and $j$. If gene flow occurred as a single pulse $t_{GF}$ generations ago, more recently than the archaic–modern split, the admixture contribution to $\bar D(x)$ decays as $e^{-t_{GF}x}$, and

$$\bar D(x) \approx A\,e^{-\lambda x} + c$$

is fitted by ordinary least squares (here over $0.02$–$1$ cM in steps of $0.001$ cM). With an exact genetic map, $\hat\lambda$ estimates $t_{GF}$.

## Expansion

Two archaic alleles at distance $x$ that entered on the same haplotype stay together in a descendant lineage only if no crossover separates them in any of the $t_{GF}$ meioses since, which happens with probability $(1-x)^{t_{GF}} \approx e^{-t_{GF}x}$ for small $x$. Admixture LD among them is proportional to this probability, while LD inherited from the shared ancestral population or created by later bottlenecks contributes the slowly varying offset $c$ and short-range excess. Restricting to low-frequency derived alleles shared with the archaic genome enriches for introgressed alleles relative to ancient shared variation. Under a gene-flow scenario the date has a clear meaning for one instantaneous pulse; for prolonged or repeated gene flow it is an average, which bounds the time of last contact from above.

## Sources

- S. Sankararaman, N. Patterson, H. Li, S. Pääbo, D. Reich, "The date of interbreeding between Neandertals and modern humans", PLoS Genetics 8 (2012) e1002947, Results and Methods ("Computation of the LD statistic on 1000 Genomes Data"), <https://doi.org/10.1371/journal.pgen.1002947> (PMC3464203).
