# Log-normal empirical Bayes shrinkage of negative binomial dispersion

**Hierarchical model.** Let $Y_{gi}$ be the read count of gene $g$ in sample $i$ ($i = 1, \dots, n$), $k(i)$ the treatment group of sample $i$, and $s_i > 0$ a known normalizing factor (for example relative library size). With an unobserved expression rate $\theta_{gi}$,

$$Y_{gi} \mid \theta_{gi} \sim \mathrm{Poisson}(s_i\,\theta_{gi}), \qquad \theta_{gi} \sim \mathrm{Gamma}\big(\text{mean } \mu_{g,k(i)},\ \text{dispersion } \phi_g\big), \qquad \log\phi_g \sim \mathcal N(m_0, \tau^2),$$

where the gamma law has shape $1/\phi_g$. Marginally $Y_{gi}$ is negative binomial with mean $\nu_{gi} = \mu_{g,k(i)}\, s_i$ and dispersion $\phi_g$:

$$\Pr(Y_{gi} = y) = \frac{\Gamma(y + \phi_g^{-1})}{\Gamma(\phi_g^{-1})\, y!}\Big(\frac{1}{1 + \nu_{gi}\phi_g}\Big)^{1/\phi_g}\Big(\frac{\nu_{gi}\phi_g}{1 + \nu_{gi}\phi_g}\Big)^{y}, \qquad \mathrm{Var}(Y_{gi}) = \nu_{gi} + \phi_g\,\nu_{gi}^2,$$

so $\phi_g$ is the squared coefficient of variation of the biological variability.

**Shrinkage estimate.** Given the means, the conditional posterior of $\phi_g$ satisfies

$$\log p(\phi_g \mid Y_{g\cdot}, \nu_{g\cdot}) = \sum_{i=1}^{n}\Big[\log\Gamma(y_{gi} + \phi_g^{-1}) - \log\Gamma(\phi_g^{-1}) - \big(y_{gi} + \phi_g^{-1}\big)\log(1 + \nu_{gi}\phi_g) + y_{gi}\log\phi_g\Big] - \frac{(\log\phi_g - m_0)^2}{2\tau^2} - \log\phi_g + \mathrm{const}.$$

The estimate $\tilde\phi_g$ is its maximizer (posterior mode) after replacing $\nu_{gi}$ by the plug-in $\hat\nu_{gi} = s_i\,\hat\mu_{g,k(i)}$ with $\hat\mu_{g,k} = \frac{1}{n_k}\sum_{i : k(i) = k} y_{gi}/s_i$. Equivalently, $\tilde\phi_g$ maximizes a penalized pseudo-likelihood with penalty $\frac{(\log\phi_g - m_0)^2}{2\tau^2} + \log\phi_g$: the first term shrinks toward the common prior value, the second penalizes large dispersions. Genes with low counts carry little information about $\phi_g$ and are shrunk more.

**Hyperparameters.** $m_0$ is estimated by the median of crude method-of-moments log-dispersions across genes; $\tau^2$ is the sample variance of those log-dispersions minus a baseline variance obtained by re-simulating data with a common dispersion (which isolates the estimation noise), floored at a small constant $c_0$.

**Test.** For two groups the Wald statistic is

$$t_g = \frac{\hat\mu_{g,1} - \hat\mu_{g,2}}{\sqrt{\widehat{\mathrm{Var}}(\hat\mu_{g,1}) + \widehat{\mathrm{Var}}(\hat\mu_{g,2})}},$$

where without normalization ($s_i \equiv 1$) $\widehat{\mathrm{Var}}(\hat\mu_{g,1}) = (\hat\mu_{g,1} + \tilde\phi_g\,\hat\mu_{g,1}^2)/n_1$; significance is assessed with a local false discovery rate against an empirical null.

## Expansion

The negative binomial marginal is the gamma–Poisson mixture integral, and the variance follows from the law of total variance: $\mathbb E[\mathrm{Var}(Y \mid \theta)] + \mathrm{Var}(\mathbb E[Y \mid \theta]) = \nu + \phi\nu^2$. The log-posterior is the sum of the negative binomial log-likelihoods (dropping the $\log y!$ terms) and the log of the log-normal density $\frac{1}{\phi\tau\sqrt{2\pi}}e^{-(\log\phi - m_0)^2/(2\tau^2)}$, whose Jacobian factor $1/\phi$ is the extra $-\log\phi$ penalty. No conjugate prior exists for the dispersion, which is why the posterior is maximized numerically rather than averaged. Compared with shrinkage toward a single common or mean-dependent trend, the log-normal prior with estimated spread $\tau^2$ keeps genuine heterogeneity of dispersions between genes with the same mean, which improved both dispersion estimation (lower mean squared error on the scale $\phi/(1 + \phi)$) and ranking of differentially expressed genes in data-based simulations.

## Sources

- H. Wu, C. Wang, Z. Wu, "A new shrinkage estimator for dispersion improves differential expression detection in RNA-seq data", Biostatistics (2013), Section 3 (motivation: log-normal spread of dispersions) and Section 4 (hierarchical model, conditional posterior Eq. (4.1), hyper-parameter estimation, Wald test and local FDR), <https://doi.org/10.1093/biostatistics/kxs033> (PMC3590927).
