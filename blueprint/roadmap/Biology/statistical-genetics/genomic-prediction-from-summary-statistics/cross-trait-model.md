# Bivariate LD-score model

Let $\mu$ be a measure on a measurable space $\Omega$ and let $n, M$ be natural numbers (a pool of genotyped individuals and the markers). A bivariate LD-score model consists of (Bulik-Sullivan et al. 2015b)

- two samples $S_1, S_2 \subseteq \{1, \dots, n\}$, possibly overlapping;
- real numbers $\rho_g$ (the genetic covariance) and $\rho_e$ (the residual cross-moment within an individual);
- real functions $\beta^{(1)}_k, \beta^{(2)}_k$ (effects on traits 1 and 2, $1 \le k \le M$) and $\varepsilon^{(1)}_i, \varepsilon^{(2)}_i$ (noise, $1 \le i \le n$) on $\Omega$, all square integrable with respect to $\mu$,

such that for all markers $k, l$ and individuals $i, i'$

- $\int \beta^{(1)}_k \beta^{(2)}_l \, d\mu = \rho_g / M$ if $k = l$, and $0$ otherwise;
- $\int \varepsilon^{(1)}_i \varepsilon^{(2)}_{i'} \, d\mu = \rho_e$ if $i = i'$, and $0$ otherwise;
- $\int \beta^{(1)}_k \varepsilon^{(2)}_i \, d\mu = 0$ and $\int \varepsilon^{(1)}_i \beta^{(2)}_k \, d\mu = 0$.

No within-trait moments or phenotype normalization are imposed, so $\rho_e$ is not identified with the phenotypic correlation.

## Sources

- B. Bulik-Sullivan et al., *An atlas of genetic correlations across human diseases and traits*, Nat. Genet. 47 (2015), 1236–1241.
