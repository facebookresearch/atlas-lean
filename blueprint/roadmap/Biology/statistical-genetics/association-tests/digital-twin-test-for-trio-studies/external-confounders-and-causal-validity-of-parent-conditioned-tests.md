# External confounders and causal validity of parent-conditioned tests

In the trio setting (offspring haplotypes $X$, parental haplotypes $A$, phenotype $Y$, SNP group $g$), a random variable $Z$ is an **external confounder** if knowledge of it does not change Mendelian transmission:

$$X \mid (A, Z = z) \overset{d}{=} X \mid (A, Z = z') \qquad \text{for all } z, z'.$$

Ancestry-related environment, socioeconomic factors and every condition arising after conception are external confounders. It follows that $Z \perp\!\!\!\perp X_g \mid (X_{-g}, A)$.

**Theorem.** If $Z$ is an external confounder, then any valid test of $H_0^g : Y \perp\!\!\!\perp X_g \mid (X_{-g}, A)$ is also a valid test of the stronger hypothesis

$$H_0'^g : \; Y \perp\!\!\!\perp X_g \mid (X_{-g}, A, Z).$$

Consequently, in a structural equation model in which genotypes cause the phenotype but not conversely and $Z$ affects $Y$ and possibly $A$, a rejection of $H_0^g$ implies that $X_g$ contains a variant with a causal effect on $Y$, not merely one correlated with $Y$ through $Z$ or through linked variants outside $g$.

## Depends on

- [Haldane HMM and the digital twin randomization test](haldane-hmm-and-the-digital-twin-randomization-test.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Conditional on the parental haplotypes, the offspring's alleles are randomized by recombination and segregation, independently of $Z$, which is the genetic analogue of assigning treatments by coin flips; conditioning additionally on $X_{-g}$ localizes the effect to region $g$. The independence $Z \perp\!\!\!\perp X_g \mid (X_{-g}, A)$ lets $Z$ be added to the conditioning set without changing the law of $X_g$, so the reference distribution used by a randomization test is unchanged. The same argument covers parent–offspring duos (fixing the haplotype from the ungenotyped parent) and any set of non-nested duos or trios in a pedigree. In admixed populations, long-range dependence that remains after conditioning on parents makes whole-chromosome tests such as the transmission disequilibrium test poor at localization, which the local nulls avoid.

## Sources

- S. Bates, M. Sesia, C. Sabatti, E. Candès, "Causal inference in genetic trio studies", Proceedings of the National Academy of Sciences 117(39) (2020) 24117–24126, Definition 1 (Eq. 7), Theorem 2 (Eq. 8), and the sections on duos and linkage disequilibrium in the trio design, <https://doi.org/10.1073/pnas.2007743117>, PMCID PMC7533659.
