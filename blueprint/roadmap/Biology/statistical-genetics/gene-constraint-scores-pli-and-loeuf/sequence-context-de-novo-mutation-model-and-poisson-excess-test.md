# Sequence-context de novo mutation model and the Poisson excess test

Let a gene $g$ have coding sites $b$ (exons with flanking essential splice sites). A sequence-context mutation model assigns to each site $b$ and each alternative base $b'$ a per-generation probability $\mu(b \to b')$ that depends on the local sequence context of $b$, and classifies each possible change by its coding impact $c(b \to b') \in \{\text{synonymous}, \text{missense}, \text{nonsense}, \text{splice}, \dots\}$. The **per-gene probability of mutation** of class $c$ is

$$p_{g,c} = \sum_{b \in g}\; \sum_{b' \ne b:\; c(b\to b') = c} \mu(b \to b').$$

In the fitted model, these relative rates are adjusted by terms for regional (1 Mb) primate divergence and local sequencing depth, and scaled to an absolute genome-wide rate of $1.2 \times 10^{-8}$ per base pair per generation.

**Excess test.** In $n$ sequenced parent–offspring trios, each child carries two newly transmitted haploid genomes, so the number $K_{g,c}$ of de novo class-$c$ mutations in gene $g$ is modeled as

$$K_{g,c} \sim \operatorname{Poisson}(\lambda_{g,c}), \qquad \lambda_{g,c} = 2n\,p_{g,c},$$

and an observed count $k$ is significant if $\Pr(K_{g,c} \ge k) = 1 - \sum_{x=0}^{k-1} e^{-\lambda_{g,c}}\lambda_{g,c}^x/x!$ is below a genome-wide threshold ($10^{-6}$ in the paper).

**Constraint.** Comparing the model's expected counts with observed rare variation in a population sample, genes with the expected amount of synonymous variation but a significant deficit of missense variation ($p < 0.001$, a one-sided normal score above $3.09$) are called constrained.

## Depends on

- [Poisson likelihood of an observed count](poisson-lik.md)

## Expansion

Summing independent rare per-site events gives a Poisson count with mean equal to the total probability. The model's synonymous predictions correlated $0.940$ with rare synonymous counts across genes, against $0.880$ for gene length alone and an estimated ceiling of $0.975$ from sampling noise. The same expected counts underlie the observed/expected ratios used by later constraint scores such as pLI and LOEUF. Methods, "Mutational model" and "Removing potential false positive constrained genes"; the exact regression for the divergence and depth terms is in the Supplementary Note.

## Sources

- K. E. Samocha, E. B. Robinson, S. J. Sanders, et al., "A framework for the interpretation of de novo mutation in human disease", Nature Genetics 46 (2014), 944–950, <https://doi.org/10.1038/ng.3050> (PMC4222185).
