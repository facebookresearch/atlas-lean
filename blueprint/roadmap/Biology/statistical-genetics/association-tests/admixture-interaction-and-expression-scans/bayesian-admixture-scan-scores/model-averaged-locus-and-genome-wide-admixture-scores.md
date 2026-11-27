# Model-averaged locus-specific and genome-wide scores in a Bayesian admixture scan

**Setting.** A sample from a two-way admixed population is genotyped on ancestry-informative markers. A hidden Markov model along each chromosome, with transition rates set by the number of generations since admixture and emissions set by the ancestral allele frequencies, yields the likelihood of the genotype data at a locus given a hypothesis about how local ancestry relates to the phenotype; unknown parameters (ancestral frequencies, admixture time, average ancestry proportion) are integrated out by Markov chain Monte Carlo rather than fixed.

**Risk models and the locus-specific score.** Fix a finite set $\mathcal M = \{m_1, \dots, m_R\}$ of risk models with prior weights $w_r > 0$, $\sum_r w_r = 1$; for a dichotomous trait $m_r$ specifies the multiplicative change in risk per copy of ancestry from one source, separately in cases and in controls, and for a quantitative trait it specifies a correlation $\rho_r$ between local ancestry and the normal-transformed trait. Let $L_\ell(m)$ be the marginal likelihood of the data at locus $\ell$ under model $m$ and $L_\ell(0)$ its likelihood when ancestry at $\ell$ is unrelated to the phenotype. The model-averaged likelihood ratio and the locus-specific score are

$$\Lambda_\ell = \sum_{r=1}^{R} w_r \frac{L_\ell(m_r)}{L_\ell(0)}, \qquad \mathrm{LOD}_\ell = \log_{10}\Lambda_\ell .$$

Choosing the set $\mathcal M$ symmetric about the null (risks $\Omega$ and $1/\Omega$, or $\pm\rho$, in pairs) makes the score test deviations toward either ancestry equally.

**Genome-wide score.** With a uniform prior over the $M$ scanned loci for the position of a single causal locus, the Bayes factor for "a risk locus exists somewhere" against "no risk locus" is the average of the locus likelihood ratios, and the genome-wide score is its logarithm,

$$\mathrm{GWS} = \log_{10}\Bigl(\frac1M\sum_{\ell=1}^{M} \Lambda_\ell\Bigr).$$

Because this is an average, not a maximum, it needs no multiple-testing correction: one locus with $\Lambda_\ell$ far above $M$ carries it, while many mildly elevated loci do not. Conventional thresholds are $\mathrm{GWS} > 2$ for significance and $> 1$ for suggestive evidence, with $\mathrm{LOD}_\ell > 5$ and $> 4$ the corresponding locus-specific thresholds.

**Credible interval for the location.** Under the same flat prior over positions on the chromosome carrying the signal, the posterior density of the causal position is proportional to $\Lambda_\ell$, so

$$\mathbb P(\text{locus at } \ell \mid \text{data}) = \frac{\Lambda_\ell}{\sum_{\ell'} \Lambda_{\ell'}},$$

and the shortest central region of the peak holding $95\%$ of this mass is the $95\%$ credible interval for the position.

## Depends on

- [Hidden Markov model](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/hmm.md): the ancestry model along a chromosome
- [Likelihood of the observations](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/likelihood.md): the locus likelihoods $L_\ell(m)$ are HMM marginal likelihoods
- [Stationary Poisson-relabeling model of local ancestry](../../../../population-structure/admixture-linkage-disequilibrium/poisson-switch-markov-model-of-local-ancestry-al.md): ancestry switches at a rate set by the time since admixture
- [Bayes posterior](../../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/bayes-posterior.md): the posterior over the causal position

## Expansion

Averaging the likelihood ratios over $\mathcal M$ is a Bayes factor with a prior on the effect size: it avoids both the optimism of maximizing over risk models and the loss of power from committing to one. Averaging again over loci converts per-locus Bayes factors into the Bayes factor for the disjunction $\bigcup_\ell \{\text{locus } \ell \text{ is causal}\}$, since under a flat prior the marginal likelihood of the alternative is $M^{-1}\sum_\ell L_\ell(\cdot)$ while the null likelihood is common to all terms; the same identity, renormalized over one chromosome, gives the posterior over position used for the credible interval. The scan's resolution is set by ancestry-segment length rather than marker density: segments span many markers, so the number of effectively independent hypotheses in a genome-wide admixture scan is of order a thousand, which is what makes locus-specific thresholds near $\mathrm{LOD} = 5$ appropriate where a single-marker association scan would need far more stringent ones.

## Sources

- C.-Y. Cheng, W. H. L. Kao, N. Patterson, A. Tandon, C. A. Haiman, T. B. Harris, C. Xing, E. M. John, C. B. Ambrosone, F. L. Brancati, J. Coresh, et al., *Admixture mapping of 15,280 African Americans identifies obesity susceptibility loci on chromosomes 5 and X*, PLoS Genetics 5 (2009), e1000490, <https://doi.org/10.1371/journal.pgen.1000490>, PMCID PMC2679192. Methods, "Estimating Local and Genome-Wide Ancestry in the African American Samples" (hidden Markov model nested in Markov chain Monte Carlo over ancestral frequencies, admixture time and ancestry proportion), "Admixture Mapping Scans Treating BMI as a Dichotomous Trait" (24 prespecified risk models averaged, locus-specific likelihood-ratio LOD, genome-wide score as the log of the average likelihood ratio, thresholds 5 and 4 for LOD and 2 and 1 for the genome-wide score), "Quantitative Admixture Mapping Scans" (risk models indexed by the correlation of local ancestry with the transformed trait) and "Credible Interval for the Position of a Genetic Locus" (flat prior, posterior from the likelihood-ratio curve, central 95% region). The Bayes-factor reading of the two averages is derived here.
