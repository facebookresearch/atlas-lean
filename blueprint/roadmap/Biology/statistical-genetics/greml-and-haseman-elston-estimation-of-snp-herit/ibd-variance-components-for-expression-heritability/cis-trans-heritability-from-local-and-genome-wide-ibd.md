# Cis and trans heritability from local and genome-wide IBD

Let $e_g = (e_{g1}, \dots, e_{gN})$ be the expression of gene $g$ in $N$ individuals, standardized to mean $0$ and variance $1$. Partition the genome into short blocks; for a pair of individuals $s, t$ let $\gamma_{g,st} \in \{0, \tfrac12, 1\}$ be the **local IBD** at the block containing gene $g$ (0, 1 or 2 haplotypes shared identical by descent, divided by 2), and let $\theta_{st} \in [0, 1]$ be the **genome-wide IBD**, the average of local IBD over all blocks, with $\theta_{ss} = \gamma_{g,ss} = 1$. Write $\Theta = (\theta_{st})$ and $\Gamma_g = (\gamma_{g,st})$.

**Single-component model.** $e_g \sim \mathcal{N}(0, V_g)$ with

$$V_g = h_g^2\, \Theta + (1 - h_g^2)\, I_N,$$

and the narrow-sense heritability $h_g^2$ is fitted by maximum likelihood.

**Cis–trans model.** Variation from regulatory variants near the gene is tracked by local IBD and the rest by genome-wide IBD:

$$V_g = h_{g,\mathrm{cis}}^2\, \Gamma_g + h_{g,\mathrm{trans}}^2\, \Theta + \bigl(1 - h_{g,\mathrm{cis}}^2 - h_{g,\mathrm{trans}}^2\bigr) I_N,$$

fitted by maximum likelihood (equivalently, fitting $h_g^2 = h_{g,\mathrm{cis}}^2 + h_{g,\mathrm{trans}}^2$ and $h_{g,\mathrm{cis}}^2$). Averaging over genes gives $h^2_{\mathrm{cis}}$ and $h^2_{\mathrm{trans}}$, and the **cis proportion** of heritable expression variation is

$$\pi_{\mathrm{cis}} = \frac{h_{\mathrm{cis}}^2}{h_{\mathrm{cis}}^2 + h_{\mathrm{trans}}^2}.$$

The two components are separable because, among relatives, local IBD at a given locus varies around the genome-wide value: for example, sibling pairs share $0$, $1$ or $2$ haplotypes at a locus with probabilities $\tfrac14, \tfrac12, \tfrac14$ while their genome-wide IBD is close to $\tfrac12$.

## Depends on

- [GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$](../greml-cov.md)

## Expansion

Under an additive model with genetic value split into a part from variants inside the gene's block and a part from the rest of the genome, the covariance of two relatives' genetic values in each part is the corresponding variance times the probability that a random allele is shared IBD in that part; for the local part this is $\gamma_{g,st}$ and for the genome-wide part it is approximately $\theta_{st}$, because a single block contributes negligibly to the genome-wide average. Local IBD is called on long-range phased haplotypes in 2 cM blocks (match at more than 95% of alleles counts as IBD, less than 85% as non-IBD); the calls reproduce the expected 0:1:2 proportions for parent–child and sibling pairs. Significance of $h_g^2 > 0$ is assessed against fits with permuted sample labels, which also give standard errors. In Icelandic family cohorts, about 37% of heritable expression variation in blood and about 24% in adipose tissue was attributed to cis regulation, with the remainder in trans.

## Sources

- A. L. Price, A. Helgason, G. Thorleifsson, S. A. McCarroll, A. Kong and K. Stefansson, "Single-tissue and cross-tissue heritability of gene expression via identity-by-descent in related or unrelated individuals", PLoS Genetics (2011), e1001317, Methods "Local IBD estimates", "Heritability estimates using genome-wide IBD only" and "Heritability estimates using both cis and trans IBD", <https://doi.org/10.1371/journal.pgen.1001317>, PMCID PMC3044684.
