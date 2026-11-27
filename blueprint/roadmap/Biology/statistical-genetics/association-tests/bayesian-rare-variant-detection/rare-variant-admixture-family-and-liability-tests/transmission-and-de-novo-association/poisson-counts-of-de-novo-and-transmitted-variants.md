# Poisson counts of de novo and transmitted variants in trios

Fix a gene and a class of rare, deleterious, dominantly acting variants, treated as a single allele $A$ with population frequency $q$ small enough that $A/A$ homozygotes are negligible; write $\mu$ for the per-generation per-chromosome mutation rate to $A$ in that gene, $\gamma \ge 1$ for the genotype relative risk of carrying $A$, and let $N$ be the number of sequenced trios (two unaffected parents and an affected child).

Three outcomes are informative in a trio: a **de novo** variant (both parents non-carriers, child a carrier), a **transmitted** variant (a carrier parent transmits $A$), and a **non-transmitted** variant (a carrier parent does not transmit $A$). Their counts over the $N$ trios, $(N_{\mathrm{dn}}, N_{\mathrm{tr}}, N_{\mathrm{nt}})$, are approximately independent Poisson variables with means

$$\mathbb{E} N_{\mathrm{dn}} = 2 N \mu \gamma, \qquad \mathbb{E} N_{\mathrm{tr}} = 2 N q \gamma, \qquad \mathbb{E} N_{\mathrm{nt}} = 2 N q .$$

For a case–control study with $N_1$ cases and $N_0$ controls, the carrier counts are likewise Poisson with means $2 N_1 q \gamma$ and $2 N_0 q$. The transmitted and non-transmitted counts therefore play the roles of case and control counts with effective sample size $N$ each, and the two designs can be pooled: with $N_{\text{ca}}$ the number of $A$ alleles in cases plus transmitted alleles and $N_{\text{cn}}$ the number in controls plus non-transmitted alleles, the joint likelihood of one gene is a product of Poisson factors in the three parameters $(\mu, q, \gamma)$, of which $\mu$ is treated as known from the gene's length and sequence context.

Under the null $\gamma = 1$ all three rates lose their dependence on risk, so a test of association is a test of $\gamma = 1$ against $\gamma > 1$ in this Poisson family. The special case that uses de novo events alone is the recurrence test: the probability of seeing at least $k$ independent de novo events in a gene of mutation rate $\mu$ among $N$ trios is the upper tail of a Poisson variable of mean $2 N \mu$, which supplies a per-gene $p$-value in place of a single genome-wide threshold on the number of hits.

## Depends on

- [Poisson likelihood of de novo counts](../../../../gene-constraint-scores-pli-and-loeuf/poisson-lik.md)

## Expansion

The Poisson approximations come from the trio genotype table. A parent is a non-carrier with probability $1 - 2q + O(q^2)$ and each of the four parental chromosomes mutates independently with probability $\mu$, so the number of de novo events among $N$ affected children is a sum of $2N$ nearly independent rare indicators, each of probability $\mu$ times the penetrance ratio $\gamma$ induced by conditioning on the child being affected; Poisson convergence for sums of rare independent indicators gives the first mean, and the same argument applied to transmission from the heterozygous parents gives the other two. Conditioning on affection is what introduces the factor $\gamma$ in the de novo and transmitted rates and leaves it out of the non-transmitted rate, which is why the triple is informative about risk at all. Independence across the three counts is an approximation, exact to first order in $q$ and $\mu$, and it is what makes the gene likelihood a product.

## Sources

- X. He, S. J. Sanders, L. Liu et al., "Integrated model of de novo and inherited genetic variants yields greater power to identify risk genes", PLoS Genetics 9 (2013), e1003671, Results ("A probabilistic model for family and case-control data", Eq. (1), Fig. 2) and Text S1, <https://doi.org/10.1371/journal.pgen.1003671>, PMCID PMC3744441.
