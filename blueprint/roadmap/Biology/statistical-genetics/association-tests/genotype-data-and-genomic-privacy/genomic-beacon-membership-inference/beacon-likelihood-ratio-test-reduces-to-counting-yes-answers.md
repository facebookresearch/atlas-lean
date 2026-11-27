# Beacon likelihood-ratio test reduces to counting yes answers

A genomic beacon over $N$ genomes answers queries "is allele $A$ present at position $y$ of chromosome $z$?" with yes ($x = 1$) or no ($x = 0$). An adversary holding a target genome queries $n$ sites at which the target carries the alternate allele and records $x_1,\dots,x_n$. Let $D_N$ be the probability that none of $N$ genomes carries the alternate allele at a queried site (under the allele-frequency distribution of the population) and $\delta$ the probability that the target's allele is missing from the beacon copy through a sequencing or calling error. Assume the answers are independent across sites, with

$$H_0 \ (\text{target not in beacon}): \Pr(x_i = 0) = D_N, \qquad H_1 \ (\text{target in beacon}): \Pr(x_i = 0) = \delta D_{N-1}.$$

Then the log-likelihood ratio is affine in the number of yes answers,

$$\Lambda = \sum_{i=1}^n \Bigl[x_i \log\frac{1-D_N}{1-\delta D_{N-1}} + (1-x_i)\log\frac{D_N}{\delta D_{N-1}}\Bigr] = nB + C\sum_{i=1}^n x_i,$$

with $B = \log\bigl(D_N/(\delta D_{N-1})\bigr)$ and $C = \log\bigl(\delta D_{N-1}(1-D_N)/(D_N(1-\delta D_{N-1}))\bigr)$. If $\delta D_{N-1} < D_N$ then $C < 0$, so rejecting $H_0$ when $\Lambda < t_\alpha$ is the same as rejecting when $\sum_i x_i > t_\alpha'$. Under $H_0$, $\sum_i x_i \sim \mathrm{Binomial}(n, 1-D_N)$, and the normal approximation gives the level-$\alpha$ threshold

$$t_\alpha' \approx n(1-D_N) + z_{1-\alpha}\sqrt{n D_N(1-D_N)},$$

where $z_{1-\alpha}$ is the standard normal quantile ($z_{0.95} \approx 1.65$). A data owner can evaluate $t_\alpha'$ from $N$ and the site-frequency distribution to see how many correct yes answers a beacon can return before membership becomes detectable.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

- [De Moivre–Laplace limit theorem, convergence in distribution](../../../../../Probability/central-limit-theorems/de-moivre-laplace-theorem/de-moivre-laplace-tendsto-in-distributio.md)

## Expansion

Expand the two Bernoulli log-likelihoods and collect the coefficient of $x_i$. The sign of $C$ is the sign of $\delta D_{N-1}(1-D_N) - D_N(1-\delta D_{N-1}) = \delta D_{N-1} - D_N$, so under the natural condition that a member's "no" answers are rarer than a non-member's, more yes answers mean stronger evidence of membership, and the test needs only the count. The threshold is the upper $\alpha$ quantile of the binomial count, approximated by the central limit theorem.

## Sources

- M. M. A. Aziz, R. Ghasemi, M. Waliullah and N. Mohammed, "Aftermath of Bustamante attack on genomic beacon service", BMC Medical Genomics 10 (Suppl. 2) (2017), <https://doi.org/10.1186/s12920-017-0278-x>, PMCID PMC5547468. Eqs. (1)–(4) and (6), restating the attack of Shringarpure and Bustamante, Am. J. Hum. Genet. 97 (2015), <https://doi.org/10.1016/j.ajhg.2015.09.010>.
