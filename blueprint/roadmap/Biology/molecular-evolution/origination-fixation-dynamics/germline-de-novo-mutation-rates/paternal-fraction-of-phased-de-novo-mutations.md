# Paternal fraction of phased de novo mutations

**Model.** For proband $i$, the numbers of de novo mutations of paternal and maternal origin are independent, $X_{P,i} \sim \operatorname{Poisson}(\lambda_{P,i})$ and $X_{M,i} \sim \operatorname{Poisson}(\lambda_{M,i})$. Each mutation is phased (assigned a parent of origin) independently with the same probability $p_i$, regardless of its origin; let $Y_{P,i}$ and $Y_{M,i}$ be the phased paternal and maternal counts.

**Proposition.** $Y_{P,i}$ and $Y_{M,i}$ are independent Poisson variables with means $p_i\lambda_{P,i}$ and $p_i\lambda_{M,i}$, and conditionally on $Y_{P,i} + Y_{M,i} = n$,

$$Y_{P,i} \sim \operatorname{Binomial}(n, r_i), \qquad r_i = \frac{\lambda_{P,i}}{\lambda_{P,i} + \lambda_{M,i}},$$

which does not depend on the phasing probability $p_i$.

**Consequence.** The expected paternal share $r_i$ of all de novo mutations, and its dependence on covariates such as paternal age, can be estimated by binomial regression of phased counts $(Y_{P,i}, Y_{M,i})$, without knowing the phasing rates. Applied to 719 trios with similar parental ages, this regression found no significant effect of paternal age on $r_i$ (logit or identity link), so the male-to-female ratio of de novo mutations is already high for young parents.

## Expansion

Independent thinning of a Poisson$(\lambda)$ count with retention probability $p$ gives a Poisson$(p\lambda)$ count, and thinning two independent Poisson counts gives independent thinned counts. For independent Poisson variables $Y_1, Y_2$ with means $\nu_1, \nu_2$, the conditional law of $Y_1$ given $Y_1 + Y_2 = n$ is binomial with success probability $\nu_1/(\nu_1 + \nu_2)$; here $\nu_1/(\nu_1+\nu_2) = p_i\lambda_{P,i}/(p_i\lambda_{P,i} + p_i\lambda_{M,i}) = r_i$, and $p_i$ cancels. Overdispersion beyond the Poisson model can be absorbed by a quasi-binomial fit, which leaves the point estimates unchanged.

## Sources

- Z. Gao, P. Moorjani, T. A. Sasani, B. S. Pedersen, A. R. Quinlan, L. B. Jorde, G. Amster, M. Przeworski, *Overlooked roles of DNA damage and maternal age in generating human germline mutations*, Proc. Natl. Acad. Sci. USA 116 (2019), <https://doi.org/10.1073/pnas.1901259116>, PMCID PMC6511033. Materials and Methods, "Test for an Effect of Parental Age on the Male Mutation Bias" (thinning argument, conditional binomial with $r_i = \lambda_{P,i}/(\lambda_{P,i}+\lambda_{M,i})$, binomial and quasi-binomial regression on 719 trios).
