# Likelihood for parental-age effects with partially phased de novo mutations

**Model.** For proband $i$ with maternal and paternal ages $G_{M,i}$, $G_{P,i}$ at conception, the expected numbers of maternal and paternal de novo mutations are linear in age,

$$\lambda_{M,i} = \beta_{0,M} + \beta_M G_{M,i}, \qquad \lambda_{P,i} = \beta_{0,P} + \beta_P G_{P,i},$$

with parameters shared by all probands, and the realized counts are independent, $X_{M,i} \sim \operatorname{Poisson}(\lambda_{M,i})$, $X_{P,i} \sim \operatorname{Poisson}(\lambda_{P,i})$. Each mutation is phased independently with probability $p_i$: $Y_{M,i} \sim \operatorname{Binomial}(X_{M,i}, p_i)$ and $Y_{P,i} \sim \operatorname{Binomial}(X_{P,i}, p_i)$ are the phased counts and $Y_{U,i} = (X_{M,i} - Y_{M,i}) + (X_{P,i} - Y_{P,i})$ the unphased count.

**Proposition.** The probability of observing $(y_M, y_P, y_U)$ for proband $i$ factorizes as

$$L_i = \underbrace{\frac{p_i^{\,y_M + y_P}(1 - p_i)^{y_U}}{y_M!\,y_P!\,y_U!}}_{\text{phasing}} \cdot \underbrace{\lambda_{M,i}^{\,y_M}\,\lambda_{P,i}^{\,y_P}\,(\lambda_{M,i} + \lambda_{P,i})^{y_U}\,e^{-(\lambda_{M,i} + \lambda_{P,i})}}_{\text{mutation parameters}}.$$

Equivalently, $Y_{M,i}$, $Y_{P,i}$, $Y_{U,i}$ are independent Poisson variables with means $p_i\lambda_{M,i}$, $p_i\lambda_{P,i}$ and $(1 - p_i)(\lambda_{M,i} + \lambda_{P,i})$. Hence the maximum-likelihood estimate of $p_i$ is $(y_{M,i} + y_{P,i})/(y_{M,i} + y_{P,i} + y_{U,i})$, and the mutation parameters maximize, up to a constant,

$$\ell(\beta) = \sum_{i}\Bigl[y_{M,i}\log\lambda_{M,i} + y_{P,i}\log\lambda_{P,i} + y_{U,i}\log(\lambda_{M,i} + \lambda_{P,i}) - (\lambda_{M,i} + \lambda_{P,i})\Bigr].$$

**Remark.** The first factor is what distinguishes partitions of the unphased mutations: assigning them so that maternal and paternal mutations are phased at very different rates is penalized, because phasing is assumed blind to parental origin. A likelihood that omits this factor treats every partition of $y_U$ as equally plausible. Intercepts $\beta_{0,M}, \beta_{0,P}$ are extrapolations to age zero and need not be nonnegative; exponential post-puberty age effects $a + \exp[b(G - 13) + c]$ can replace the linear means and be compared by AIC.

## Depends on

- [Paternal fraction of phased de novo mutations](paternal-fraction-of-phased-de-novo-mutations.md)

## Expansion

Sum over the unobserved split $X_{M,i} = y_M + j$, $X_{P,i} = y_P + y_U - j$, $j = 0, \dots, y_U$. Each term is

$$\binom{y_M + j}{y_M}\binom{y_P + y_U - j}{y_P} p^{\,y_M + y_P}(1-p)^{y_U}\, e^{-\lambda_M - \lambda_P}\frac{\lambda_M^{\,y_M + j}\lambda_P^{\,y_P + y_U - j}}{(y_M + j)!\,(y_P + y_U - j)!},$$

which simplifies to $\frac{p^{y_M+y_P}(1-p)^{y_U}}{y_M!\,y_P!}e^{-\lambda_M-\lambda_P}\lambda_M^{y_M}\lambda_P^{y_P}\cdot\frac{\lambda_M^{j}\lambda_P^{y_U-j}}{j!\,(y_U-j)!}$. The binomial theorem gives $\sum_j \lambda_M^j\lambda_P^{y_U-j}/(j!(y_U-j)!) = (\lambda_M + \lambda_P)^{y_U}/y_U!$, which yields $L_i$. The independent-Poisson form follows by Poisson thinning: phased maternal, phased paternal and unphased mutations are the three cells of a multinomial thinning of the merged Poisson stream.

## Sources

- Z. Gao, P. Moorjani, T. A. Sasani, B. S. Pedersen, A. R. Quinlan, L. B. Jorde, G. Amster, M. Przeworski, *Overlooked roles of DNA damage and maternal age in generating human germline mutations*, Proc. Natl. Acad. Sci. USA 116 (2019), <https://doi.org/10.1073/pnas.1901259116>, PMCID PMC6511033. Materials and Methods, "Estimation of Sex-Specific Mutation Parameters with a Model-Based Approach" (model, summed likelihood, simplified $L_i$, log-likelihood), and "Test for Alternative Models for Parental Age Effects" (exponential effects, $P = 13$, AIC comparison). The independent-Poisson restatement is derived here.
