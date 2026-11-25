# Random-effects model of LD-score regression

Let $\mu$ be a measure on a measurable space $\Omega$ and let $N, M$ be natural numbers (individuals and markers). An LD-score model consists of a real number $h^2$ (the SNP heritability) and real functions $\beta_1, \dots, \beta_M$ (the marker effects) and $\varepsilon_1, \dots, \varepsilon_N$ (the environmental noise) on $\Omega$, square integrable with respect to $\mu$, such that for all markers $k, l$ and individuals $i, i'$

- $\int \beta_k \beta_l \, d\mu = h^2 / M$ if $k = l$, and $0$ otherwise;
- $\int \varepsilon_i \varepsilon_{i'} \, d\mu = 1 - h^2$ if $i = i'$, and $0$ otherwise;
- $\int \beta_k \varepsilon_i \, d\mu = 0$.

The measure is arbitrary and no means are imposed; when $\mu$ is a probability measure and effects and noise have mean zero, these are the covariance conditions of the model of Bulik-Sullivan et al. (2015). The genotype matrix is not part of the model: all expectations are conditional on it.

## Sources

- B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working Group of the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price, B. M. Neale, *LD Score regression distinguishes confounding from polygenicity in genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
