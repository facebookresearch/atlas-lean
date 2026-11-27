# Binomial sampling error of panel-based tumor mutational burden

Tumor mutational burden is the number of counted somatic coding mutations (base substitutions and short indels) per megabase of coding sequence examined. Suppose a tumor carries mutations independently at each coding base with probability $p = \tau / 10^{6}$, where $\tau > 0$ is its true TMB in mutations per megabase, and a panel examines $n = 10^{6} m$ bases ($m > 0$ megabases). The mutation count is $M \sim \mathrm{Binomial}(n, p)$ and the panel estimate is $\hat{\tau} = M/m$. Then

$$\mathbb{E}[\hat{\tau}] = \tau, \qquad \operatorname{Var}(\hat{\tau}) = \frac{\tau\,(1 - \tau/10^{6})}{m} \approx \frac{\tau}{m}, \qquad \operatorname{CV}(\hat{\tau}) = \frac{\sqrt{\operatorname{Var}(\hat{\tau})}}{\tau} \approx \frac{1}{\sqrt{\tau\, m}} .$$

So the relative error is governed by the expected number of mutations $\tau m$ in the examined territory: it falls as the inverse square root of panel size and of TMB itself, and it grows quickly once the panel covers less than about half a megabase.

## Depends on

- [Binomial probability mass function](../detection-power-for-somatic-mutations/binom-pmf.md)

## Proof depends on

- [Variance of the binomial law](../../../Probability/distributions/discrete/binomial-distribution/variance-id-map-cast-binomial.md)

## Proof sketch

Unbiasedness and the variance follow from $\mathbb{E}[M] = np$ and $\operatorname{Var}(M) = np(1-p)$, divided by $m$ and $m^2$. The source simulated exactly this binomial downsampling, $1000$ replicates at whole-exome TMB of $100$, $20$ and $10$ mutations/Mb over $0$ to $10$ Mb sequenced, and found that the variance rises sharply below $0.5$ Mb, while a panel of about $1.1$ Mb tracked whole-exome TMB closely. Counting synonymous mutations enlarges $M$ and therefore reduces sampling noise, which is why they were included even though synonymous changes create no neoantigens. Real panels also deviate from the model through local mutation-rate heterogeneity, which adds overdispersion, and through the exclusion of known driver hotspots, which the source removes because panel genes are enriched for them.

## Sources

- Z. R. Chalmers et al., "Analysis of 100,000 human cancer genomes reveals the landscape of tumor mutational burden", Genome Medicine 9 (2017) 34, Methods, "WES analysis of TCGA data" and "Tumor mutational burden". <https://doi.org/10.1186/s13073-017-0424-2> (PMC5395719)
