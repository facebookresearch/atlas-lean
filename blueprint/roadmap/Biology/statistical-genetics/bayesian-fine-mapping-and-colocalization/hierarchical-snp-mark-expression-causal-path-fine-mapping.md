# Hierarchical SNP–mark–expression causal-path fine-mapping

At a locus with $s$ SNPs (genotype vector $G$), $t$ chromatin-mark peaks (signal vector $H$) and one gene (expression $E$), assume a single causal path: one causal SNP $c$ acts on one causal mark $d$, which acts on expression,

$$h_d = G\beta_g + \epsilon_g, \qquad E = H\beta_h + \epsilon_h, \qquad \epsilon_g \sim N(0, 1 - \sigma_g^2),\ \epsilon_h \sim N(0, 1 - \sigma_h^2),$$

where $\beta_g$ is nonzero only at $c$, $\beta_h$ only at $d$, and $\sigma_g^2, \sigma_h^2$ are the variances explained at the two levels. Let $\Sigma_g$ be the SNP correlation (LD) matrix, $\Sigma_h$ the mark correlation matrix, $C_g$ and $C_h$ the indicator vectors of the causal SNP and mark, and $N$ the sample size.

**Mark-to-expression level.** The Wald statistics $Z_{h_k} = \hat\beta_{h_k}/\mathrm{SE}(\hat\beta_{h_k})$ satisfy $Z_{h_k} \sim N(\lambda_{h_k}, 1)$ with noncentrality $\lambda_{h_k} = \beta_{h_k}\sqrt{\mathrm{Var}(h_k)}\sqrt{N}/\sigma_h$, and jointly $Z_h \mid C_h \sim N(\Sigma_h\Lambda_{h,d}, \Sigma_h)$. With prior $\Lambda_{h,d} \mid C_h \sim N(0, \Sigma_{C,h})$, $\Sigma_{C,h} = \sigma_h^2\,\mathrm{Diag}(C_h) + \mathrm{Diag}(\epsilon)$, integrating out the effect gives

$$Z_h \mid C_h \sim N\big(0,\ \Sigma_h + \Sigma_h\Sigma_{C,h}\Sigma_h\big).$$

**SNP-to-mark level.** The $s \times t$ matrix of SNP–mark Wald statistics is matrix-variate normal,

$$Z_g \mid C_g, C_h \sim \mathcal{MN}(M, \Sigma_g, \Sigma_h), \qquad M_{jk} = \Sigma_{g,jc}\,\Sigma_{h,kd}\,\lambda_{c,d},$$

so the signal at SNP $j$ and mark $k$ is the causal noncentrality attenuated by LD with $c$ and by correlation with $d$ ($\lambda_{c,d}$ is approximated by the observed causal $Z$-score).

**Posterior of a causal path.** With a uniform prior over the $st$ SNP–mark pairs,

$$P(C_g, C_h \mid Z_g, Z_h) = \frac{P(Z_h \mid C_h)\,P(Z_g \mid C_g, C_h)}{\sum_{(C_g', C_h')} P(Z_h \mid C_h')\,P(Z_g \mid C_g', C_h')},$$

from which credible sets of SNPs, of marks, and of whole SNP→mark→gene paths are formed. Non-uniform priors (for example by distance to the transcription start site) enter as $P(C_g, C_h)$ in the numerator.

## Depends on

- [Credible set of variants](is-credible-set.md)
- [Bayes posterior](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/bayes-posterior.md): the path posterior

## Proof depends on

- [The marginal of a linear-Gaussian model](../../../Probability/distributions/continuous/gaussian-conditioning/map-linear-add-of-indep-fun.md): integrating out the mark effect

## Expansion

The construction extends single-trait summary-statistic fine-mapping, where LD makes the marginal $Z$-scores multivariate normal with mean $\Sigma\lambda$, to a two-level causal chain. At the upper level the model is a one-causal-mark fine-mapping problem, and the Gaussian integral over the unknown effect gives the closed-form covariance $\Sigma_h + \Sigma_h\Sigma_{C,h}\Sigma_h$; a small diagonal $\epsilon$ keeps $\Sigma_{C,h}$ positive definite. At the lower level the joint correlation of SNP–mark statistics factorizes as a Kronecker product of LD and mark correlation, which is the matrix-variate normal. Multiplying the two likelihoods treats the levels as conditionally independent given the path, and normalizing over all $st$ single-path configurations yields path posteriors (Eqs. (1)–(18) of the source).

## Sources

- M. Roytman, G. Kichaev, A. Gusev, B. Pasaniuc, "Methods for fine-mapping with chromatin and expression data", PLOS Genetics (2018), <https://doi.org/10.1371/journal.pgen.1007240> (PMC5843356).
