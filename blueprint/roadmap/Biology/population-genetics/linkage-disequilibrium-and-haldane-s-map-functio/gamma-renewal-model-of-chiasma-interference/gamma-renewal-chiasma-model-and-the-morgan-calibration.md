# Gamma renewal model of chiasma placement and the Morgan calibration

**Model (no obligate chiasma).** On a bivalent of map length $\ell$ Morgans, chiasmata are the points of a renewal process: successive inter-chiasma distances $d_1, d_2, \dots$ are independent with the gamma density

$$f_v(d) = \frac{(2v)^v}{\Gamma(v)}\, d^{\,v-1} e^{-2vd}, \qquad d > 0,$$

that is $\operatorname{Gamma}$ with shape $v \ge 1$ and scale $1/(2v)$, so $\mathbb E d = 1/2$ Morgan (50 cM) and $\operatorname{Var} d = 1/(4v)$. The process is started far enough before the chromosome to reach stationarity, and only the points falling inside the chromosome are kept. Each chiasma independently involves one of the two chromatids of each homolog, chosen uniformly and independently of all other chiasmata (no chromatid interference); after all chiasmata are resolved, one chromatid from each bivalent is segregated independently to form a haploid product.

**Proposition (calibration and the no-interference limit).**
1. The chiasma intensity is $2$ per Morgan. A fixed chromatid participates in each chiasma with probability $1/2$, so its crossover process is the $1/2$-thinning of the chiasma process, with intensity $1$ per Morgan: the expected number of crossovers along a chromatid of map length $\ell$ is $\ell$, the defining property of the Morgan.
2. The shape $v$ is an interference parameter: the inter-chiasma coefficient of variation is $v^{-1/2}$, so $v = 1$ is the exponential (interference-free) case and $v > 1$ spaces chiasmata more regularly than a Poisson process.
3. At $v = 1$ the chiasma process is Poisson of rate $2$ per Morgan and its $1/2$-thinning is Poisson of rate $1$. Hence the number of crossovers separating two loci $d$ Morgans apart on one chromatid is $\operatorname{Poisson}(d)$, and the recombination fraction is Haldane's map function $\bigl(1 - e^{-2d}\bigr)/2$.

**Obligate chiasma variant.** To force at least one chiasma per bivalent, place the first chiasma uniformly on the chromosome and run the gamma renewal process outward in both directions from it. Conditioning this way distorts the marginal spacing, so the shape and scale can no longer be read off the target mean; they are calibrated by simulation, for instance by accepting parameters whose simulated mean $u$ and standard deviation $\delta$ of the chiasma count on a bivalent of $100$ cM make the discrepancy $D' = (2 - u)^2/(0.05^2 + \delta^2)$ small, under the pseudo-likelihood $L = e^{-D'}$ targeting two chiasmata per Morgan.

## Depends on

- [Mean of the gamma law](../../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/integral-id-gamma-measure.md)
- [Variance of the gamma law](../../../../Probability/distributions/continuous/gamma-distribution/gamma-moments/variance-id-gamma-measure.md)
- [Poisson process](../../../../Probability/point-processes/poisson-processes/is-poisson-process.md)
- [Thinning](../../../../Probability/point-processes/poisson-processes/thinning-2.md)
- [Haldane's map function](../haldane.md)
- [Haldane's map function from Poisson crossovers](../poisson-measure-real-odd.md)

## Expansion

A renewal process with interarrival mean $1/2$ has intensity $2$ in the stationary regime, which is statement 1 before thinning; independent chromatid choice marks each point with probability $1/2$ independently, so the marked process has intensity $1$ and, in the Poisson case, is again Poisson by the thinning theorem. Statement 2 is the gamma moment identity $\operatorname{Var}/(\mathbb E)^2 = 1/v$. For statement 3, a Poisson process of rate $2$ per Morgan thinned to rate $1$ puts $\operatorname{Poisson}(d)$ points in an interval of length $d$, and recombination between the endpoints occurs exactly when that count is odd, which is Haldane's map function. Positive interference ($v > 1$) does not change the expected number of crossovers, only their spacing, so it leaves the map length intact while shortening the tails of the recombination-fraction distribution relative to Haldane's. Competing models are compared by a chromosome-wise discrepancy between simulated and observed crossover counts and intercrossover distances, $D_j = \sum_i (u_{i,\mathrm{sim}} - u_{i,\mathrm{obs}})^2/(\delta^2_{i,\mathrm{sim}} + \delta^2_{i,\mathrm{obs}})$ for feature $j$ over chromosomes $i$, combined into $L = \prod_j e^{-D_j}$.

## Sources

- W. Wong, E. A. Wenger, D. L. Hartl, D. F. Wirth, *Modeling the genetic relatedness of Plasmodium falciparum parasites following meiotic recombination and cotransmission*, PLoS Computational Biology 14 (2018), e1005923, <https://doi.org/10.1371/journal.pcbi.1005923>, PMCID PMC5777656. Methods, "Simulating meiosis and recombination" (gamma distribution with shape $v$ and scale $1/(2v)$, mean inter-chiasma distance 50 cM, independent sister-chromatid choice per chiasma, obligate-chiasma construction, ABC-MCMC distance $D'$ and pseudo-likelihood) and "Model selection: Non-obligate vs obligate chiasma model" (the chromosome-wise discrepancy and product pseudo-likelihood). The thinning, Morgan calibration and Haldane limit are derived here.
