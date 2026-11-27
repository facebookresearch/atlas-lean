# Trio genotype-combination posterior for de novo mutations

At a biallelic site, let $G_M$, $G_F$ and $G_C$ be the genotypes of mother, father and child, and let $L(D \mid G)$ be the per-individual genotype likelihood of the observed bases $D$. Enumerate the possible trio genotype combinations: on the autosomes there are $27$, of which $15$ obey Mendelian inheritance, $10$ carry one de novo mutation and $2$ carry two; on the X chromosome of a female offspring there are $18$ (the father being haploid), with $8$ Mendelian, $8$ single and $2$ double; for a male offspring, who inherits his X from his mother, only $6$ mother–offspring combinations exist, $4$ Mendelian and $2$ single de novo.

Given a per-site mutation rate $\mu$, with $n$ combinations carrying one de novo mutation and $m$ carrying two, assign each genotype combination $C$ the prior weight

$$P_C \;=\; \begin{cases} 1 - n\mu - m\mu^2 & \text{if } C \text{ follows Mendel's laws,}\\ \mu & \text{if } C \text{ implies one de novo mutation,}\\ \mu^2 & \text{if } C \text{ implies two de novo mutations.}\end{cases}$$

These weights are unnormalised (each Mendelian combination receives $1 - n\mu - m\mu^2$, so they do not sum to $1$); only their ratios matter, since the posterior is normalised over the combinations. The posterior probability of a combination is then proportional to the product of the three genotype likelihoods and this prior,

$$P(G_M, G_F, G_C \mid D) \;\propto\; L(D_M \mid G_M)\, L(D_F \mid G_F)\, L(D_C \mid G_C)\, P_C ,$$

normalized over the enumerated combinations. The trio is assigned its most likely combination, and every site whose assigned combination violates Mendelian inheritance is reported as a candidate de novo mutation with that normalized posterior as its confidence. Population allele frequencies may be added as independent priors on the parental genotypes under Hardy–Weinberg proportions, $P(G)$ determined by the estimated allele dosages $p$ and $q$ among the founders.

## Depends on

- [Mendel's law of segregation](../../../population-genetics/hardy-weinberg-law/transmit.md): which trio combinations obey Mendelian inheritance
- [Hardy–Weinberg proportions](../../../population-genetics/hardy-weinberg-law/offspring-apply.md): the optional allele-frequency prior on parental genotypes
- [Bayes' rule for countably many hypotheses](../../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/bayes-posterior-apply-singleton.md): the normalized posterior over the enumerated combinations

## Expansion

The model is a discrete Bayesian network with the Mendelian transmission matrix as its only structure, so the calculation is exact and scales linearly in the number of sites and trios. Two parameters control the operating point. The mutation prior trades sensitivity against specificity: a larger $\mu$ recovers more true de novo mutations at the cost of false positives, and the useful value depends on sequencing depth, with permissive values ($10^{-5}$) suited to low-coverage data and values near the per-base human germline rate ($1.5 \times 10^{-8}$) to deep data. The allele-frequency prior is what gives the model its advantage at low coverage: a site where a parent is poorly covered but the alternate allele is common in the population is explained better by an untyped inherited allele than by a new mutation, so the false-positive rate falls where it is otherwise highest. The same posterior supports phasing — combining transmission-based phase with read-backed phase assigns a parental origin to a de novo mutation when reads span an adjacent heterozygous site in the child.

## Sources

- L. C. Francioli, M. Cretu-Stancu, K. V. Garimella, et al., "A framework for the detection of de novo mutations in family-based sequencing data", *European Journal of Human Genetics* 25 (2017), 227–233, <https://doi.org/10.1038/ejhg.2016.147> (PMC5255947). Materials and Methods, genotype-combination priors and posteriors, Equations (1)–(4).
