# Case–control shift and calibration of a log-risk polygenic score

Let $D \in \{0, 1\}$ be the status for a **rare** disease and let the true polygenic risk score $\mathrm{PRS}_T$ act on the log-risk scale, $\Pr(D = 1 \mid G) = \exp(\mathrm{PRS}_T)$. Suppose $\mathrm{PRS}_T \sim \mathcal{N}(\mu, \sigma^2)$ in the population; $\sigma^2$ is the heritability on the log-risk scale.

**True score.** Among cases, $\mathrm{PRS}_T \sim \mathcal{N}(\mu + \sigma^2, \sigma^2)$: the case distribution is the population distribution shifted by $\sigma^2$. Hence any discrimination measure is a function of $\sigma^2$ alone; for the area under the ROC curve, comparing cases with the population (which, for a rare disease, is essentially the control distribution), $\mathrm{AUC} = \Phi(\sigma/\sqrt2)$.

**Estimated score.** Let $\mathrm{PRS}_E$ be an estimated score with $(\mathrm{PRS}_E, \mathrm{PRS}_T)$ jointly normal, $s^2 = \operatorname{Var}(\mathrm{PRS}_E)$, $c = \operatorname{Cov}(\mathrm{PRS}_E, \mathrm{PRS}_T)$ and $r = c/s$. Then:
1. among cases, $\mathrm{PRS}_E$ is normal with variance $s^2$ and mean shifted by $c$ (not $s^2$);
2. the log odds (approximately the log risk) given the estimated score is $\log\frac{\Pr(D = 1 \mid \mathrm{PRS}_E)}{\Pr(D = 0 \mid \mathrm{PRS}_E)} = \frac{c}{s^2}\,\mathrm{PRS}_E + \text{const}$, so $\mathrm{PRS}_E$ must be multiplied by the **calibration factor** $c/s^2$ to estimate risk without bias;
3. the calibrated score $(c/s^2)\mathrm{PRS}_E$ has variance $r^2$, which plays the role of $\sigma^2$ for the estimated score and determines its stratification and discrimination ($\mathrm{AUC} = \Phi(r/\sqrt2)$).

Adding SNPs that carry signal raises $c$; adding noise SNPs raises $s^2$ without raising $c$ and so lowers $r$.

## Proof sketch

Bayes' rule gives the case density $f_{\text{case}}(x) \propto \Pr(D = 1 \mid x) f(x) = e^{x}\phi_{\mu,\sigma^2}(x)$, and completing the square, $x - (x - \mu)^2/(2\sigma^2) = -(x - \mu - \sigma^2)^2/(2\sigma^2) + \text{const}$, so exponential tilting of a normal shifts its mean by its variance. For the estimated score, $\Pr(D = 1 \mid \mathrm{PRS}_E) = \mathbb{E}[e^{\mathrm{PRS}_T} \mid \mathrm{PRS}_E]$, and $\mathrm{PRS}_T \mid \mathrm{PRS}_E$ is normal with mean linear in $\mathrm{PRS}_E$ with slope $c/s^2$ and constant variance, so the log risk is $(c/s^2)\mathrm{PRS}_E$ plus a constant; tilting the normal law of $\mathrm{PRS}_E$ by this exponent shifts its mean by $(c/s^2)s^2 = c$. For two normal laws with common standard deviation $\tau$ and mean difference $\delta$, $\mathrm{AUC} = \Phi(\delta/(\tau\sqrt2))$; with $\delta = \sigma^2, \tau = \sigma$ this is $\Phi(\sigma/\sqrt2)$, and with $\delta = c, \tau = s$ it is $\Phi(r/\sqrt2)$. The AUC formulas use the rare-disease approximation in which controls follow the population law.

## Proof depends on

- [Exponential tilting of a centered Gaussian](../../../../Probability/statistical-estimation/contiguity-and-le-cam-s-lemmas/gaussian-real-with-density-exp.md)

## Sources

- N. Chatterjee, J. Shi and M. García-Closas, "Developing and evaluating polygenic risk prediction models for stratified disease prevention", *Nature Reviews Genetics* 17 (2016), 392–406, Box 2 ("Risk distribution and discrimination with true and estimated PRS for a rare disease"), <https://doi.org/10.1038/nrg.2016.27> (PMC6021129).
