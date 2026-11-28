# PICS: probabilistic identification of causal SNPs from a lead association

Consider a locus with a lead SNP $A$ whose association signal is $s_A = -\log_{10}P_A$, and candidate SNPs $B$ with linkage disequilibrium $r^2_{AB}$ to $A$ (in practice those with $r^2 > 0.5$).

**Signal model.** Under the Armitage trend test, $\chi^2 \approx (n-1)\,r_{GY}^2$ with $r_{GY}$ the correlation between genotype and phenotype; for a neutral SNP $B$ in LD $r^2_{AB}$ with the single causal variant $A$, $\chi^2_B \approx r^2_{AB}\,\chi^2_A$, so the expected signal of a neutral SNP scales linearly with its $r^2$ to the causal SNP. If SNP $B$ is causal with signal $s$, the signal at a SNP with LD $r^2$ to $B$ is modeled as normal with

$$m = r^2\,s, \qquad \sigma = \sqrt{1 - r^k}\,\frac{\sqrt{s}}{2},$$

where $r$ is the absolute value of the correlation coefficient between the two SNPs (so $r^2$ is the usual LD measure) and $k$ is an empirical constant ($k = 6.4$; values in $[6,8]$ behave similarly), fitted to permutation simulations over odds ratios $1.1$–$2.0$ and varying case/control sizes.

**Posterior.** With equal prior probability for every SNP to be causal, Bayes' theorem gives

$$P(B\ \text{causal} \mid A\ \text{lead}) \propto P(A\ \text{lead} \mid B\ \text{causal}),$$

and the probabilities are normalized to sum to $1$ over the candidate set. In the permutation-based version $P(A\ \text{lead}\mid B\ \text{causal})$ is the fraction of simulations with the causal signal fixed at $B$ in which $A$ is the top SNP; in the general version it is evaluated from the normal model above using the LD of each candidate to the lead SNP, so that only the lead SNP's $P$-value and an LD reference panel are required.

## Expansion

The relation $\chi^2_{\text{neutral}} \approx r^2\chi^2_{\text{causal}}$ follows because the trend statistic is $n$ times the squared correlation of genotype and phenotype, and correlation with the phenotype is transmitted through LD with the causal variant. Statistical fluctuation makes the causal SNP not always the top SNP, so a SNP in near-perfect LD ($r \to 1$, $\sigma \to 0$) with the lead receives probability comparable to the lead, whereas SNPs whose expected signal $r^2 s$ falls many $\sigma$ below the observed lead signal receive little.

## Sources

- Kyle Kai‐How Farh, Alexander Marson and Jiang Zhu, "Genetic and epigenetic fine mapping of causal autoimmune disease variants", Nature (2014), <https://doi.org/10.1038/nature13835> (PMC4336207). Methods, "Probabilistic identification of causal SNPs (PICS)".
