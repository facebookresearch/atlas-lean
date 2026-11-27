# Embedding estimator of the uncovered probability

**Setting.** An environment is an urn with countably many colours (species), colour $i$ having relative abundance $p_i > 0$, $\sum_i p_i = 1$; balls are drawn independently with replacement. After a first sample, let $C$ be the set of colours already observed and $\theta = \sum_{i \notin C} p_i$ the **uncovered probability**, the fraction of the environment belonging to unsampled colours. Classical point predictors are the Good–Turing statistic (singletons divided by sample size) and Robbins' estimator, the proportion of colours seen exactly once in a sample of size $n+1$, which is unbiased for the expected uncovered probability after $n$ draws with mean squared error at most $1/(n+1)$.

**Impossibility (fixed sample sizes).** For any predetermined sample size, a non-randomized algorithm based on a continuous one-to-one function of the sample can predict $\theta$ conditionally unbiasedly if and only if the urn consists of a known, equidistributed set of colours. Unbiased prediction of $\theta$ therefore requires a random sample size.

**Embedding construction.** Conditionally on the first sample, keep drawing until $r \ge 1$ balls with colours outside $C$ have been observed, and attach the draws to the points of an independently simulated homogeneous Poisson process of rate $1$ on $[0, \infty)$. By Poisson thinning, the points carrying colours outside $C$ form a homogeneous Poisson process of rate $\theta$, independent of the others, so the arrival time $T$ of the $r$-th such point is $\mathrm{Gamma}(r, \theta)$:

$$P(T \in dt \mid C) = \frac{\theta^r t^{r-1} e^{-\theta t}}{(r-1)!}\,dt, \qquad t > 0.$$

Hence $(r-1)/T$ is an unbiased predictor of $\theta$ for $r \ge 2$, the uniformly minimum variance unbiased one based on the $r$ exponential spacings, with variance $\theta^2/(r-2)$ for $r \ge 3$; $\psi(r) - \log T$ is unbiased for $\log\theta$, with variance $\psi'(r)$, where $\psi$ is the digamma function ($\psi(1) = -\gamma_{\mathrm{Euler}}$); and for constants $0 \le a < b$ with $P(a \le \Gamma(r,1) \le b) = 1-\alpha$, the interval $[a/T, b/T]$ contains $\theta$ with exact probability $1 - \alpha$, conditionally on $C$. All predictors are strongly consistent as $r \to \infty$.

## Depends on

- [The Good–Turing identity for the missing mass](../../../not-yet-classified/good-turing/expect-missing-mass.md)
- [Thinning](../../../../Probability/point-processes/poisson-processes/thinning-2.md)

## Expansion

Without Poissonization, the counts of different colours in a fixed-size sample are multinomially dependent, which is what blocks unbiased prediction of $\theta$; the auxiliary Poisson clock is simulated independently of the urn and removes that dependence exactly, not asymptotically, so no assumption on how the data were collected is needed. Repeating the procedure along a long sample gives sequential predictions of coverage at increasing depth, and in simulated environments modelled on human-gut and soil communities these predictions were markedly more accurate than sequential Robbins-type estimates, whose errors persist from one depth to the next. Prediction intervals for $\theta$ can exclude zero, unlike singleton-based bounds when no singletons are seen.

## Sources

- M. E. Lladser, R. Gouet, J. Reeder, "Extrapolation of urn models via poissonization: accurate measurements of the microbial unknown", PLoS ONE 6(6): e21105 (2011), Eq 1, Theorems 1–3 and the Embedding algorithm (Table 1), <https://doi.org/10.1371/journal.pone.0021105>, PMCID PMC3125174.
