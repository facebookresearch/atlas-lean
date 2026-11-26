# Random match probability of a biallelic SNP barcode

A barcode is the vector of alleles of a haploid genome at $L$ biallelic SNPs. Suppose the SNPs segregate independently (linkage equilibrium) and the minor allele at locus $\ell$ has population frequency $q_\ell \in [0, \tfrac12]$. For two genomes sampled independently from the population, the probability that their barcodes are identical is

$$P_{\mathrm{match}} = \prod_{\ell=1}^{L} \big(q_\ell^2 + (1 - q_\ell)^2\big) = \prod_{\ell=1}^{L} \big(1 - 2 q_\ell (1 - q_\ell)\big).$$

Each factor is strictly decreasing in $q_\ell$ on $[0, \tfrac12]$ and at least $\tfrac12$, so $P_{\mathrm{match}} \ge 2^{-L}$ with equality if and only if every $q_\ell = \tfrac12$. For $L = 24$ the bound is $2^{-24} \approx 6.0 \times 10^{-8}$; if every locus had minor allele frequency $0.35$, $P_{\mathrm{match}} = 0.545^{24} \approx 4.7 \times 10^{-7}$.

## Expansion

Two independent haploid genomes carry the same allele at locus $\ell$ with probability $q_\ell^2 + (1-q_\ell)^2$, the homozygosity at that locus; independence across loci multiplies these probabilities. Since $2q(1-q)$ (the expected heterozygosity) is maximal at $q = \tfrac12$, markers with high minor allele frequency carry the most identifying information, which is why the Plasmodium falciparum barcode uses 24 SNPs sampled across the genome with average minor allele frequency above $35\%$. Blood-stage parasites are haploid, so a single-clone infection yields one allele per locus; a polyclonal infection shows both alleles at some loci, and quantitative allele ratios from the genotyping assay indicate the mixture. The formula assumes random sampling from one population: in low-transmission settings with clonal propagation or strong population structure, identical barcodes are far more frequent than the product predicts, which is itself the epidemiological signal such barcodes are used to detect.

## Sources

- R. Daniels, S. K. Volkman, D. A. Milner et al., "A general SNP-based molecular barcode for Plasmodium falciparum identification and tracking", Malaria Journal 7 (2008), 223, <https://doi.org/10.1186/1475-2875-7-223> (PMC2584654).
