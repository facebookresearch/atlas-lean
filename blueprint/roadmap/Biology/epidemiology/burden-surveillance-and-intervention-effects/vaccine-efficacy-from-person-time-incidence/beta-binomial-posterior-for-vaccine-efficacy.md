# Beta-binomial posterior for vaccine efficacy

Under the two-arm Poisson model of
[vaccine efficacy as one minus the incidence rate ratio](vaccine-efficacy-as-one-minus-the-incidence-rate-ratio.md),
restricted to the open parameter space $\lambda_v, \lambda_p > 0$, so that $\mathrm{VE} \in (-\infty, 1)$,
let $r = T_v / T_p$ be the ratio of surveillance times and $n = X_v + X_p$ the total number of cases.
Conditionally on $n$,

$$X_v \mid n \;\sim\; \mathrm{Binomial}(n, \theta), \qquad
\theta \;=\; \frac{r\,(1-\mathrm{VE})}{1 + r\,(1-\mathrm{VE})},$$

and the map $\mathrm{VE} \mapsto \theta$ is a strictly decreasing bijection from $(-\infty, 1)$ onto
$(0, 1)$ with inverse

$$\mathrm{VE} \;=\; 1 - \frac{\theta}{r\,(1-\theta)}.$$

If $\theta$ is given a $\mathrm{Beta}(a, b)$ prior with $a, b > 0$, its posterior after observing
$X_v = x$ is $\mathrm{Beta}(a + x,\ b + n - x)$. Posterior quantiles and tail probabilities of
$\mathrm{VE}$ are those of $\theta$ transported by the decreasing inverse map: for any threshold
$v_0 < 1$,

$$\Pr(\mathrm{VE} > v_0 \mid x) \;=\; \Pr\Bigl(\theta < \frac{r(1-v_0)}{1 + r(1-v_0)} \Bigm| x\Bigr).$$

## Depends on

- [Vaccine efficacy as one minus the incidence rate ratio](vaccine-efficacy-as-one-minus-the-incidence-rate-ratio.md)

## Proof sketch

If $X_v \sim \mathrm{Poisson}(\mu_v)$ and $X_p \sim \mathrm{Poisson}(\mu_p)$ are independent, then
$X_v \mid X_v + X_p = n$ is binomial with success probability $\mu_v / (\mu_v + \mu_p)$; with
$\mu_a = \lambda_a T_a$ and $\lambda_v = (1 - \mathrm{VE})\lambda_p$ this ratio is the stated
$\theta$, and the nuisance rate $\lambda_p$ cancels. Beta-binomial conjugacy then gives the posterior.
The BNT162b2 protocol used the prior $\mathrm{Beta}(0.700102, 1)$, whose mean
$0.700102/1.700102 \approx 0.4118$ corresponds (for $r = 1$) to $\mathrm{VE} = 1 - 0.4118/0.5882 \approx 0.30$,
the efficacy threshold of the success criterion. With $x = 8$, $n = 170$ and $r = 2.214/2.222$ the
posterior is $\mathrm{Beta}(8.700102, 163)$; transporting its 2.5%, 50% and 97.5% quantiles gives
$\mathrm{VE} \approx 0.903,\ 0.948,\ 0.976$, reproducing the reported 95% credible interval
90.3% to 97.6%, and $\Pr(\mathrm{VE} > 0.3 \mid x) > 0.9999$.

## Sources

- F. P. Polack, S. J. Thomas, N. Kitchin et al., "Safety and Efficacy of the BNT162b2 mRNA Covid-19 Vaccine", *New England Journal of Medicine* 383 (2020), <https://doi.org/10.1056/NEJMoa2034577> (PMC7745181), "Statistical Analysis" (credible interval and posterior probability of efficacy above 30% from a Bayesian beta-binomial model) and Table 2 footnotes (prior $\mathrm{Beta}(0.700102, 1)$ "adjusted for the surveillance time").
