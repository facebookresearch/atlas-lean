# Heritability explained by local ancestry in a two-way admixed population

Let two ancestral populations $P_0, P_1$ have allele frequencies $p_{s,0}, p_{s,1} \in (0,1)$ at biallelic SNPs $s = 1, \dots, N$. An admixed diploid individual $i$ draws a global ancestry proportion $\theta_i$ from a distribution with mean $\theta \in (0,1)$. Given $\theta_i$, its maternal and paternal local ancestries $\gamma_{i,s,M}, \gamma_{i,s,P} \in \{0,1\}$ (number of copies from $P_1$) are independent $\mathrm{Ber}(\theta_i)$, and each haplotype carries the allele $g_{i,s,M} = \gamma_{i,s,M} Z_{i,s,1} + (1 - \gamma_{i,s,M}) Z_{i,s,0}$ with independent $Z_{i,s,k} \sim \mathrm{Ber}(p_{s,k})$ (similarly for $P$). Put $g_{i,s} = g_{i,s,M} + g_{i,s,P}$ and $\gamma_{i,s} = \gamma_{i,s,M} + \gamma_{i,s,P}$. Then (the variance formula holding exactly when $\theta_i \equiv \theta$, and approximately otherwise)

$$\mu_{g,s} = \mathbb{E}[g_{i,s}] = 2\big(\theta p_{s,1} + (1 - \theta) p_{s,0}\big),$$

$$\sigma_{g,s}^2 = 2\Big[\theta(1-\theta)(p_{s,1} - p_{s,0})^2 + \theta p_{s,1}(1 - p_{s,1}) + (1-\theta) p_{s,0}(1 - p_{s,0})\Big],$$

and local ancestry has mean $\mu_\gamma = 2\theta$ and variance $\sigma_\gamma^2 \approx 2\theta(1-\theta)$ (exact when $\theta_i \equiv \theta$; in practice $\sigma_\gamma^2$ is estimated empirically). Let the standardized phenotype follow the additive model

$$y_i = \sum_{s} \beta_s \bar g_{i,s} + \varepsilon_i, \qquad \bar g_{i,s} = \frac{g_{i,s} - \mu_{g,s}}{\sigma_{g,s}}, \qquad \operatorname{Var} y_i = 1, \qquad h^2 = \sum_s \beta_s^2,$$

with $\varepsilon_i$ independent of genotype and ancestry. Define the heritability explained by local ancestry as $h_\gamma^2 = \operatorname{Var}\big(\mathbb{E}[y_i \mid \gamma_{i,1}, \dots, \gamma_{i,N}]\big)$ and the causal-variant differentiation

$$F_{STC} = \sum_s \frac{\beta_s^2}{h^2} \, \frac{(p_{s,1} - p_{s,0})^2}{\sigma_{g,s}^2}.$$

If the standardized local ancestries at distinct causal SNPs are treated as uncorrelated, then

$$h_\gamma^2 = 2\,\theta(1 - \theta)\, h^2\, F_{STC}.$$

In practice $h_\gamma^2$ is the variance-component ratio $\sigma_\gamma^2/(\sigma_\gamma^2 + \sigma_\varepsilon^2)$ of the mixed model $Y \sim N(0, K_\gamma \sigma_\gamma^2 + I \sigma_\varepsilon^2)$, where $K_\gamma$ is the kinship matrix built from local ancestry in place of genotypes (with $\theta_i$ and principal components as fixed effects), and $h^2$ is recovered as $h_\gamma^2 / \big(2\theta(1-\theta) F_{STC}\big)$.

## Depends on

- [GREML covariance matrix](../greml-and-haseman-elston-estimation-of-snp-herit/greml-cov.md)

## Expansion

Writing $\gamma_{i,s,M} - \theta$ for the centred local ancestry, each haplotype allele decomposes as $(\gamma_{i,s,M} - \theta)(Z_{i,s,1} - Z_{i,s,0}) + \big[\theta(Z_{i,s,1} - p_{s,1}) + (1-\theta)(Z_{i,s,0} - p_{s,0})\big] + \text{const}$, so

$$\bar g_{i,s} = \frac{\sigma_\gamma}{\sigma_{g,s}} \bar\gamma_{i,s} (Z_{i,s,1} - Z_{i,s,0}) + \delta_{i,s},$$

where $\delta_{i,s}$ does not depend on local ancestry. Conditioning on all local ancestries replaces $Z_{i,s,1} - Z_{i,s,0}$ by $p_{s,1} - p_{s,0}$, giving $\mathbb{E}[y_i \mid \gamma] = \sum_s \beta_s (\sigma_\gamma/\sigma_{g,s}) \bar\gamma_{i,s} (p_{s,1} - p_{s,0})$; its variance, with the cross terms dropped and $\sigma_\gamma^2 = 2\theta(1-\theta)$, is $2\theta(1-\theta)\sum_s \beta_s^2 (p_{s,1}-p_{s,0})^2/\sigma_{g,s}^2$. Local ancestry segments span megabases and tag every causal variant inside them, rare or poorly genotyped ones included, so $h_\gamma^2$ carries information on total narrow-sense $h^2$ rather than on SNP heritability; because the individuals are unrelated, the estimate is not inflated by shared environment or by epistasis as twin estimates can be. Restricting $K_\gamma$ to segments of one chromosome partitions $h^2$ along the genome.

## Sources

- N. Zaitlen, B. Pasaniuc, S. Sankararaman et al., "Leveraging population admixture to characterize the heritability of complex traits", Nature Genetics 46 (2014), <https://doi.org/10.1038/ng.3139> (PMC4244251). Online Methods, Equations (1)-(15).
