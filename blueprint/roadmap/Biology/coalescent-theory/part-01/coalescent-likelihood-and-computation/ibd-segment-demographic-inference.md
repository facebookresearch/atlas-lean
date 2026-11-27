# Demographic inference from segments of identity by descent

Browning and Browning (2015, Appendix) model a segment shared identical by descent by two haplotypes whose most recent common ancestor lived $g$ generations ago: there are $g$ meioses on each side, and under Haldane's model crossovers occur independently at rate $1/100$ per centimorgan per meiosis. On a chromosome of infinite length, a segment drawn at random from the list of segments then has length exponentially distributed with rate $2g/100 = g/50$ per cM, while a segment selected because it covers a fixed position has, on each side of that position, an exponential length with rate $g/50$, so its total length is Erlang with shape $2$ and rate $g/50$. Hence $P(l > C \mid \mathrm{TMRCA} = g) = (Cg/50 + 1)e^{-Cg/50}$, and under the Wright–Fisher model with sizes $N[g]$ the joint probability with the time is $\frac{1}{2N[g]}\prod_{h = g^*}^{g - 1}(1 - \frac{1}{2N[h]})(Cg/50 + 1)e^{-Cg/50}$ for $g \ge g^*$, where the product starts at the most recent generation $g^*$ whose size is estimated: the Wright–Fisher probability $P(\mathrm{TMRCA} = g) = \frac{1}{2N[g]}\prod_{h = 1}^{g - 1}(1 - \frac{1}{2N[h]})$ is used with $1 - \frac{1}{2N[h]}$ taken to be $1$ for $h < g^*$ (Equation A1), with explicit corrections for segments censored by a chromosome end. Their estimator IBDNe fits $N$ by an iterative generalized EM algorithm with method-of-moments steps: given the current $N$, the observed and expected amounts of IBD are allocated to generations, and a piecewise exponential growth function is refitted (Material and Methods, Overview). Ralph and Coop (2013, Methods) model detection by a length-dependent probability of missing a true block and an exponential length-error law, and treat the recovery of the distribution of ancestry times from block counts as an ill-conditioned inverse problem whose point estimates need a regularizing penalty.

## Expansion

1. The two-haplotype model: the time to the most recent common ancestor under a size history, and Haldane crossovers along each of the $2g$ meioses.
2. The exponential length of a random segment and the Erlang length of a segment covering a fixed point, and the resulting tail $P(l > C \mid g)$.
3. Censoring at chromosome ends and the detection and length-error model.
4. The mixture over generations, the IBDNe iteration, and regularization of the inverse problem, as estimators rather than exact identities.

## Sources

- S. R. Browning and B. L. Browning, Accurate non-parametric estimation of recent effective population size from segments of identity by descent, Am. J. Hum. Genet. 97 (2015), 404–418, Material and Methods and Appendix. <https://doi.org/10.1016/j.ajhg.2015.07.012>
- P. Ralph and G. Coop, The geography of recent genetic ancestry across Europe, PLoS Biol. 11 (2013), e1001555, Methods. <https://doi.org/10.1371/journal.pbio.1001555>
