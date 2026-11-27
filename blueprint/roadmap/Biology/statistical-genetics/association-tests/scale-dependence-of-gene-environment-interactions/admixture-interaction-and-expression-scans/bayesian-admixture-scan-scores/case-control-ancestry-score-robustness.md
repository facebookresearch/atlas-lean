# Case-control ancestry score and its robustness to a misspecified ancestry mean

**Setting.** In a two-way admixed sample, let $\bar A^{\text{cases}}_\ell$ and $\bar A^{\text{controls}}_\ell$ be the average local ancestry from one source at locus $\ell$ among cases and controls, and let $\bar A^{\text{cases}}$, $\bar A^{\text{controls}}$ be the corresponding genome-wide averages. The case-control score compares the two locus-specific deviations,

$$Z_\ell = \frac{\bigl(\bar A^{\text{cases}}_\ell - \bar A^{\text{cases}}\bigr) - \bigl(\bar A^{\text{controls}}_\ell - \bar A^{\text{controls}}\bigr)}{\widehat{\mathrm{sd}}},$$

with $\widehat{\mathrm{sd}}$ the standard deviation of the numerator, estimated so that $Z_\ell$ is approximately standard normal when no locus is associated with the phenotype.

**Proposition (robustness).** Suppose the inferred local ancestry at locus $\ell$ carries an additive systematic bias $b_\ell$ that does not depend on phenotype, so that the inferred average in each group is the true average plus $b_\ell$, and suppose the reference level used for the genome-wide average is likewise shifted by a common constant $c$ in both groups. Then $b_\ell$ and $c$ cancel in the numerator of $Z_\ell$: the score is unchanged. By contrast, a case-only score, which compares $\bar A^{\text{cases}}_\ell$ with $\bar A^{\text{cases}}$ alone, is shifted by $b_\ell - c$ and can produce a spurious signal.

**Use.** This is what makes the case-control score the appropriate statistic on the X chromosome, where the chromosome-wide average ancestry differs from the autosomal average and is itself hard to estimate because the chromosome is short; any error in that reference affects cases and controls alike. With ancestry segments long enough that a genome scan tests on the order of $10^3$ effectively independent hypotheses, a two-sided threshold $|Z_\ell| > 4.06$ (nominal $p < 5\times 10^{-5}$) corresponds to a corrected significance level near $0.05$.

## Depends on

- [Model-averaged locus-specific and genome-wide scores in a Bayesian admixture scan](model-averaged-locus-and-genome-wide-admixture-scores.md): the admixture-scan setting and local-ancestry inference the averages come from

## Expansion

Writing each inferred group average as truth plus bias, the difference of differences is

$$\bigl[(A^{\text{cases}}_\ell + b_\ell) - (A^{\text{cases}} + c)\bigr] - \bigl[(A^{\text{controls}}_\ell + b_\ell) - (A^{\text{controls}} + c)\bigr],$$

in which $b_\ell$ and $c$ appear once with each sign. The price of the cancellation is power: the score uses only the contrast between the groups, so it discards the information in the cases' own deviation from their genome average, which is exactly what the case-only score exploits, and it needs control samples that the case-only design does not. The two scores are therefore complementary, and a locus is most convincing when both support it. Neither score protects against a bias that acts differently on cases and controls, for instance one arising from differential genotyping quality or from phenotype-correlated genome-wide ancestry.

## Sources

- C.-Y. Cheng, W. H. L. Kao, N. Patterson, A. Tandon, C. A. Haiman, T. B. Harris, C. Xing, E. M. John, C. B. Ambrosone, F. L. Brancati, J. Coresh, et al., *Admixture mapping of 15,280 African Americans identifies obesity susceptibility loci on chromosomes 5 and X*, PLoS Genetics 5 (2009), e1000490, <https://doi.org/10.1371/journal.pgen.1000490>, PMCID PMC2679192. Methods, "Admixture Mapping Scans Treating BMI as a Dichotomous Trait" (case-control score as the difference of locus-specific ancestry deviations between cases and controls, standard normal null, threshold $|Z| > 4.06$ from roughly 1,000 independent ancestry chunks, and the argument that a systematic bias at a locus affects cases and controls alike, which is why the score is used on the X chromosome). The cancellation statement is formalized here.
