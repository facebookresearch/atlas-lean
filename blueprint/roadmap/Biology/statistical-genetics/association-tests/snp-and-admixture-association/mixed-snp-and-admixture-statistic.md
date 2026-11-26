# Mixed SNP and admixture association statistic

Keep the setting of the two component scores: a case–control sample from a two-way admixed population, allelic odds ratio $R$ assumed equal across ancestries, control allele frequencies $p_A, p_E$, and ancestry odds ratio $\Omega$.

**Key identity.** Under a single causal variant with odds ratio $R$, the ancestry odds ratio is not free: carrying one extra $E$ chromosome raises risk only through the chance that this chromosome carries the risk allele, so

$$\Omega(R, p_A, p_E) = \frac{R\,p_E + (1 - p_E)}{R\,p_A + (1 - p_A)},$$

the ratio of the per-chromosome relative risks of the two ancestries. Thus $\Omega = 1$ when $p_A = p_E$ or $R = 1$, and $\Omega$ departs from one in proportion to the ancestral frequency difference.

**The statistic.** Substituting this $\Omega$ into the [case-only admixture likelihood](case-only-admixture-association.md) and multiplying by the [likelihood conditioned on local ancestry](snp-association-conditioned-on-local-ancestry.md) gives a single likelihood in $(R, p_A, p_E)$,

$$L_{\mathrm{MIX}}(R, p_A, p_E) = L_{\mathrm{SNP1}}(R, p_A, p_E) \cdot L_{\mathrm{ADM}}\big(\Omega(R, p_A, p_E)\big),$$

and the test of $R = 1$ is the likelihood-ratio statistic

$$\chi^2_{\mathrm{MIX}} = 2 \log \frac{\max_{R, p_A, p_E} L_{\mathrm{MIX}}}{\max_{p_A, p_E} L_{\mathrm{MIX}}(1, \cdot)} \;\sim\; \chi^2_1 .$$

The two factors are independent: one conditions on local ancestry, the other uses only local ancestry. Summing the two $\chi^2_1$ statistics instead would give a valid $\chi^2_2$ test, but spending a second degree of freedom on a parameter that the single-causal-variant assumption determines costs power; the mixed statistic keeps one degree of freedom.

**Behaviour.** On real admixed genotypes with simulated case–control phenotypes the mixed score was well calibrated ($\lambda_{\mathrm{GC}} \approx 1.00$) and more powerful than a trend test corrected for genome-wide ancestry: about $8\%$ more genome-wide significant findings at an odds ratio of $1.5$ over all SNPs, about $24\%$ more over the decile of SNPs whose ancestral frequencies differ by at least $0.4$, and about $11\%$ more at imputed SNPs. Against a test conditioned on local ancestry only — the analogue of association in a single ancestral population — the gains were $13\%$ and $67\%$ respectively.

**Diagnostic from the difference.** Since the $\chi^2_2$ sum generalizes the mixed likelihood by freeing $\Omega$, the difference of the two statistics is itself approximately $\chi^2_1$ and tests whether the observed admixture signal is larger than the fitted odds ratio can explain, as happens when several causal variants lie in the same ancestry block.

## Depends on

- [SNP association conditioned on local ancestry](snp-association-conditioned-on-local-ancestry.md)
- [Case-only admixture association](case-only-admixture-association.md)

## Expansion

The identity for $\Omega$ is the derivation that makes the two data sources commensurable. Take a chromosome of ancestry $a$: it carries the risk allele with probability $p_a$ and so confers relative risk $R p_a + (1 - p_a)$ relative to a chromosome with no risk allele; the ratio over the two ancestries is the multiplicative risk per $E$ chromosome, which is exactly what the admixture likelihood calls $\Omega$. Because this expression is monotone in $R$ for $p_E > p_A$, the admixture factor sharpens the profile likelihood in $R$ rather than merely adding an independent test, and its contribution grows with $|p_E - p_A|$, which is why the power gain is concentrated in the differentiated decile. The construction assumes one causal variant with ancestry-invariant effect; when that fails — heterogeneous effects, or multiple causal variants in one block — the fitted $\Omega$ misfits the data, which is what the difference diagnostic detects.

## Sources

- B. Pasaniuc, N. Zaitlen, G. Lettre et al., "Enhanced statistical tests for GWAS in admixed populations: assessment using African Americans from CARe and a Breast Cancer Consortium", PLoS Genetics 7 (2011), e1001371, Methods ("MIX: mixed SNP and admixture association"), Tables 1–4 and Text S1, <https://doi.org/10.1371/journal.pgen.1001371>, PMCID PMC3080860.
