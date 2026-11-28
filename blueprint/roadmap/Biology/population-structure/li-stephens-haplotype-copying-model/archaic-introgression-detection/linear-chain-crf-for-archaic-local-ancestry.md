# Linear-chain conditional random field for archaic local ancestry

Let $x$ be the observed data along a phased haplotype of a test population (its alleles at SNPs $1, \dots, n$, a reference panel assumed free of archaic ancestry, an archaic genome, ancestral states and genetic distances $d_i$ between SNPs $i - 1$ and $i$), and let $y = (y_1, \dots, y_n) \in \{0, 1\}^n$ be the unobserved labels, $y_i = 1$ meaning that the allele at SNP $i$ was inherited from archaic gene flow. A **linear-chain conditional random field** models

$$p_\lambda(y \mid x) = \frac{1}{Z_\lambda(x)} \exp\Bigl(\sum_{i=1}^{n} \sum_k \lambda_k\, e_k(y_i, x, i) + \sum_{i=2}^{n} \mu\, h(y_{i-1}, y_i, d_i)\Bigr),$$

with $Z_\lambda(x)$ the sum of the exponential over all $2^n$ label sequences. The **emission features** $e_k$ used for Neanderthal ancestry are:

- indicators of single-SNP allele patterns: the test haplotype carries the derived allele, every reference-panel haplotype carries the ancestral allele and the archaic genome carries a derived allele (evidence for archaic ancestry, positive weight); or the derived allele of the test haplotype is polymorphic in the reference panel but absent from the archaic genome (evidence against);
- a multi-SNP feature comparing, in non-overlapping 100 kb windows, the divergence of the test haplotype from the closer archaic haplotype with its minimum divergence from all reference haplotypes.

The **transition feature** $h$ is a small-distance approximation to the log transition probabilities of the two-state Markov process of local ancestry after admixture, so neighboring labels are correlated over a genetic-distance scale set by the time since gene flow.

**Inference.** For fixed weights, the posterior marginals $p_\lambda(y_i = 1 \mid x)$ are computed exactly in $O(n)$ time by the forward–backward recursions. The weights are estimated by maximizing the $L_2$-penalized conditional log-likelihood $\sum \log p_\lambda(y \mid x) - c \|\lambda\|^2$ on haplotypes simulated with known labels under a fitted demographic model, using limited-memory BFGS.

## Depends on

- [Stationary Poisson-relabeling model of local ancestry](../../admixture-linkage-disequilibrium/poisson-switch-markov-model-of-local-ancestry-al.md)

## Expansion

Unlike a hidden Markov model, a conditional random field normalizes over labels given all the data, so overlapping, non-independent features of the whole haplotype (single-site patterns and window divergences) can be combined without modeling their joint distribution. The conditional log-likelihood is concave in $(\lambda, \mu)$, with gradient equal to observed minus expected feature counts; the expectations come from the same forward–backward pass. Training on simulations sidesteps the lack of labeled real data; in the application, gene flow was placed about 1,900 generations ago at a 3% archaic fraction, and recombination hotspots and low-coverage allele-detection loss were simulated. Thresholding the marginals yields introgressed haplotypes, whose genomic distribution (for example depletion near genes and on the X chromosome) is the object of downstream inference.

## Sources

- S. Sankararaman, S. Mallick, M. Dannemann, K. Prüfer, J. Kelso, S. Pääbo, N. Patterson and D. Reich, "The genomic landscape of Neanderthal ancestry in present-day humans", Nature (2014), Online Methods "Conditional Random Field for inferring Neandertal local ancestry", "Feature functions" and "Parameter Estimation" (mathematical details in Supplementary Information 1), <https://doi.org/10.1038/nature12961>, PMCID PMC4072735.
- J. Lafferty, A. McCallum and F. Pereira, "Conditional random fields: probabilistic models for segmenting and labeling sequence data", Proceedings of the 18th International Conference on Machine Learning (2001), 282–289.
