# Empirical-Bayes Bayes factor for rare-variant association

Let gene $i$ have data $x_i$ — the de novo, transmitted, non-transmitted and case–control counts of one mutation class — with likelihood $L(x_i \mid q_i, \gamma_i)$ the [Poisson product](poisson-counts-of-de-novo-and-transmitted-variants.md) in the variant frequency $q_i$ and relative risk $\gamma_i$, the mutation rate being known. Model a fraction $\pi$ of genes as risk genes:

- under $H_0$: $\gamma_i = 1$ and $q_i \sim \rho_0$;
- under $H_1$: $\gamma_i \ne 1$, with $\gamma_i \sim \rho_\gamma$ a law on $(0, \infty)$ (in the source $\mathrm{Gamma}(\bar\gamma\beta, \beta)$) and $q_i \sim \rho_1$.

The **evidence** for each model is the marginal likelihood

$$\mathrm{E}_1(x_i) = \iint L(x_i \mid q, \gamma)\, \rho_1(q)\, \rho_\gamma(\gamma)\, \mathrm{d}q\, \mathrm{d}\gamma, \qquad \mathrm{E}_0(x_i) = \int L(x_i \mid q, 1)\, \rho_0(q)\, \mathrm{d}q,$$

and the gene's **Bayes factor** is $\mathrm{BF}_i = \mathrm{E}_1(x_i)/\mathrm{E}_0(x_i)$. The hyperparameters of $\rho_0, \rho_1, \rho_\gamma$ are fitted once by maximizing the marginal likelihood of the data over all genes (empirical Bayes), so information is borrowed across the genome while each gene keeps its own rate; the significance of $\mathrm{BF}_i$ is calibrated by simulating data under $H_0$.

**Independent mutation classes multiply.** If several classes (for example loss-of-function and damaging missense) are modelled with separate hyperparameters and assumed independent given the gene, the gene's total Bayes factor is the product of its per-class Bayes factors.

**Relation to a likelihood-ratio test.** $\mathrm{BF}_i$ is approximately the likelihood ratio evaluated at posterior-mean parameter estimates,

$$\mathrm{BF}_i \approx \frac{L(x_i \mid \tilde{q}_i, \tilde{\gamma}_i)}{L(x_i \mid \tilde{q}_i^{\,0}, 1)},$$

where $\tilde q_i$ interpolates between the gene's own maximum-likelihood frequency and the genome-wide prior mean. This is where the power comes from: for most genes the per-gene maximum-likelihood estimate of $q_i$ is zero and a plain likelihood ratio test is degenerate, while the shrunk estimate is strictly positive and finite.

## Depends on

- [Poisson counts of de novo and transmitted variants in trios](poisson-counts-of-de-novo-and-transmitted-variants.md)

## Expansion

Integrating out $(q, \gamma)$ rather than maximizing is what makes uninformative data harmless: a gene with no de novo events contributes a de novo Bayes factor close to one, so the product over classes is unaffected, whereas combining $p$-values by Fisher's method penalizes the gene for the near-one de novo $p$-value. That asymmetry, together with the shrinkage of $q_i$, accounts for the power gain over both the recurrence test and $p$-value meta-analysis; in simulations calibrated to autism exome data the Bayes-factor test recovered several times as many true risk genes at a fixed false-discovery rate. The empirical-Bayes step also estimates the mixture itself: fitting $\rho_1$ and $\rho_0$ separately shows that the frequency of damaging alleles in risk genes is smaller than in other genes, as expected under stronger purifying selection, without ever classifying individual genes.

## Sources

- X. He, S. J. Sanders, L. Liu et al., "Integrated model of de novo and inherited genetic variants yields greater power to identify risk genes", PLoS Genetics 9 (2013), e1003671, Results ("Hierarchical Bayes framework", Eqs. (2)–(3)) and Methods, <https://doi.org/10.1371/journal.pgen.1003671>, PMCID PMC3744441.
