# Maximum credible population allele frequency for a Mendelian variant

Consider a Mendelian disorder with population prevalence $\pi$ and a candidate variant with penetrance $\phi \in (0, 1]$. Let the **maximum genetic contribution** $G$ be the largest proportion of cases attributable to any single gene, and the **maximum allelic contribution** $A$ the largest proportion of cases (dominant model) or of a gene's pathogenic alleles (recessive model) attributable to any single variant; both are upper bounds taken from case series or variant databases. Assuming Hardy–Weinberg proportions and that each affected individual's disease is due to the gene in question, a pathogenic allele cannot exceed the **maximum credible population allele frequency**

$$q_{\max} = \begin{cases} \dfrac{\pi\, A}{2\,\phi}, & \text{dominant (one causal allele per case)},\\[2ex] A\,\sqrt{\dfrac{\pi\, G}{\phi}}, & \text{recessive (biallelic cases)}. \end{cases}$$

To allow for sampling variance in a reference sample of $AN$ genotyped chromosomes, the **maximum tolerated allele count** is the upper one-sided $95\%$ point of a Poisson law with mean $AN \cdot q_{\max}$: the smallest integer $c$ with

$$\Pr\big(\mathrm{Poisson}(AN \cdot q_{\max}) \le c\big) \ge 0.95 .$$

A variant observed more than $c$ times (in a major continental subpopulation, using that subpopulation's $AN$) is evidence, at nominal one-sided level $5\%$, against a population frequency at most $q_{\max}$; it is not a proof that the variant cannot cause the disorder, since even at frequency $q_{\max}$ the count exceeds $c$ with probability up to $5\%$, and the bound rests on the assumed values of $\pi$, $G$, $A$ and $\phi$. Conversely, a variant's **filtering allele frequency** is the largest population frequency that its observed count still rejects at the $5\%$ level, i.e. the lower one-sided $95\%$ confidence bound on its true frequency; it is disease-independent, and the variant is flagged for a disorder whenever its filtering allele frequency is at least that disorder's $q_{\max}$.

**Example (hypertrophic cardiomyopathy).** With $\pi = 1/500$, $A = 0.02$ (the most common variant explains at most about $2\%$ of cases) and $\phi = 0.5$, $q_{\max} = (1/500)(0.02)/(2 \cdot 0.5) = 4.0 \times 10^{-5}$. With $AN = 121{,}412$ chromosomes the Poisson mean is $4.86$ and the maximum tolerated count is $9$ (it is $5$ for fully penetrant alleles, Poisson mean $2.43$).

## Proof sketch

Dominant case: the cases attributable to one variant have population frequency at most $\pi A$; carriers of a variant at allele frequency $q$ number $2q$ per individual to first order (heterozygotes), of whom a fraction $\phi$ are affected, so $2 q \phi \le \pi A$. Recessive case: cases due to the gene have frequency at most $\pi G$; under Hardy–Weinberg the probability of carrying two pathogenic alleles of the gene is $q_{\mathrm{gene}}^2$, so $q_{\mathrm{gene}}^2 \phi \le \pi G$, and a single variant accounts for at most a fraction $A$ of the gene's pathogenic alleles, giving $q \le A\sqrt{\pi G/\phi}$. The Poisson step treats the observed allele count as approximately binomial with tiny success probability; an exceedance of the one-sided $95\%$ point is a nominal level-$5\%$ test of the specified frequency, not a categorical exclusion. In the original application to hypertrophic cardiomyopathy, $477$ of $479$ variants reported as pathogenic or likely pathogenic in a published case cohort fell below the threshold (the other two were reclassified on review). Of $601$ ClinVar pathogenic or likely pathogenic variants, $43$ were too common in at least one ExAC population; on curation $42$ of these lacked sufficient evidence of pathogenicity, but one had convincing evidence (observed twice, outside the $95\%$ but within the $99\%$ bound). The post-curation false-positive rates were therefore $0/477$ in the published cohort and $1/559$ in ClinVar, so the filter does not retain every pathogenic variant.

## Depends on

- [Hardy–Weinberg proportions](../../population-genetics/hardy-weinberg-law/offspring-apply.md)

## Sources

- N. Whiffin, E. Minikel, R. Walsh et al., "Using high-resolution variant frequencies to empower clinical genome interpretation", Genetics in Medicine (2017), Materials and Methods and Results ("Defining maximum credible population AF", Tables 1–2), <https://doi.org/10.1038/gim.2017.26> (PMC5563454).
