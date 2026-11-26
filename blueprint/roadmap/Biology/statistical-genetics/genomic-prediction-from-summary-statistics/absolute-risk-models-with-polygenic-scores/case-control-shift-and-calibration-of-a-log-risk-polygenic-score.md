# Case–control shift and calibration of a log-risk polygenic score

Let the true polygenic risk score $T = \mathrm{PRS}_T$ satisfy $T \sim \mathcal{N}(\mu, \sigma^2)$ in the population, with $\sigma^2 > 0$. Define the **case law** as the exponential tilt of the population law by $T$: for every event $A$ in the genotype space,

$$\Pr_{\mathrm{case}}(A) = \frac{\mathbb{E}[e^{T}\, \mathbf{1}_A]}{\mathbb{E}[e^{T}]}, \qquad \text{density ratio } \frac{e^{T}}{\mathbb{E}[e^{T}]} = e^{T - \mu - \sigma^2/2}.$$

**Interpretation.** For a rare disease $D \in \{0,1\}$ with log-risk score, $\Pr(D = 1 \mid G) \approx e^{T}$, so Bayes' rule makes the case law approximately this tilt and the control law approximately the population law. This is an approximation, not an exact Bernoulli model: for any nondegenerate Gaussian $T$, $\Pr(T > 0) > 0$, so $e^{T} > 1$ with positive probability, and making the disease rare (lowering $\mu$) shrinks but never removes that event. The results below are exact statements about the tilted law; their risk and log-odds readings inherit the rare-disease approximation.

**True score.** Under the case law, $T \sim \mathcal{N}(\mu + \sigma^2, \sigma^2)$: the case distribution is the population distribution shifted by $\sigma^2$. Hence any discrimination measure between the case and population laws is a function of $\sigma^2$ alone; for the area under the ROC curve, $\mathrm{AUC} = \Phi(\sigma/\sqrt2)$, and $\sigma^2$ is called the heritability on the log-risk scale.

**Estimated score.** Let $E = \mathrm{PRS}_E$ be an estimated score with $(E, T)$ jointly normal in the population, $m = \mathbb{E}[E]$, $s^2 = \operatorname{Var}(E) > 0$ (a nonconstant score), $c = \operatorname{Cov}(E, T)$ and $r = c/s$. Then:
1. under the case law, $E$ is normal with variance $s^2$ and mean $m + c$ (shifted by $c$, not $s^2$);
2. the density ratio of $E$ under the case law to $E$ under the population law is $\exp\{(c/s^2)(E - m) - c^2/(2s^2)\}$, so its logarithm is linear in $E$ with slope $c/s^2$; in the rare-disease reading this is the log risk (approximately the log odds) given $E$ up to a constant, and $E$ must be multiplied by the **calibration factor** $c/s^2$ to estimate risk without bias;
3. the calibrated score $(c/s^2)E$ has variance $r^2$, which plays the role of $\sigma^2$ for the estimated score and determines its stratification and discrimination ($\mathrm{AUC} = \Phi(r/\sqrt2)$ between the case and population laws).

Adding SNPs that carry signal raises $c$; adding noise SNPs raises $s^2$ without raising $c$ and so lowers $r$.

## Proof sketch

The case density is $f_{\text{case}}(x) \propto e^{x}\phi_{\mu,\sigma^2}(x)$, and completing the square, $x - (x - \mu)^2/(2\sigma^2) = -(x - \mu - \sigma^2)^2/(2\sigma^2) + \text{const}$, so exponential tilting of a normal shifts its mean by its variance. For the estimated score, the density ratio of $E$ is $\mathbb{E}[e^{T} \mid E]/\mathbb{E}[e^{T}]$. Since $s^2 > 0$, $T \mid E \sim \mathcal{N}(\mu + (c/s^2)(E - m),\ \sigma^2 - c^2/s^2)$, so $\mathbb{E}[e^{T} \mid E] = \exp\{\mu + (c/s^2)(E - m) + (\sigma^2 - c^2/s^2)/2\}$, and dividing by $e^{\mu + \sigma^2/2}$ gives the stated ratio. Tilting the normal law of $E$ by the exponent $(c/s^2)E$ shifts its mean by $(c/s^2)s^2 = c$. For two normal laws with common standard deviation $\tau$ and mean difference $\delta$, $\mathrm{AUC} = \Phi(\delta/(\tau\sqrt2))$; with $\delta = \sigma^2, \tau = \sigma$ this is $\Phi(\sigma/\sqrt2)$, and with $\delta = c, \tau = s$ it is $\Phi(r/\sqrt2)$. Reading these as case–control AUCs uses the rare-disease approximation in which controls follow the population law.

## Proof depends on

- [Exponential tilting of a centered Gaussian](../../../../Probability/statistical-estimation/contiguity-and-le-cam-s-lemmas/gaussian-real-with-density-exp.md)

## Sources

- N. Chatterjee, J. Shi and M. García-Closas, "Developing and evaluating polygenic risk prediction models for stratified disease prevention", *Nature Reviews Genetics* 17 (2016), 392–406, Box 2 ("Risk distribution and discrimination with true and estimated PRS for a rare disease"; its log-risk model is a rare-disease approximation), <https://doi.org/10.1038/nrg.2016.27> (PMC6021129).
