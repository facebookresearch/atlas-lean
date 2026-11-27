# Pooled-testing prevalence estimator, optimal pool size and dilution correction

**Perfect tests.** Sample $nN$ individuals at random from a population with unknown prevalence $p \in (0,1)$ and form $n$ pools of size $N$. Let $X_i^{(N)} = 1$ if pool $i$ tests positive, i.e. contains at least one infected individual, so the $X_i^{(N)}$ are i.i.d. Bernoulli with parameter $1 - (1-p)^N$, and let $\bar X_n^{(N)} = \frac1n\sum_{i=1}^n X_i^{(N)}$.

**Statement.**

1. *Estimator.* $\hat p = 1 - (1 - \bar X_n^{(N)})^{1/N}$ is a strongly consistent and asymptotically normal estimator of $p$, and an asymptotic $(1-\alpha)$ confidence interval is

$$
\mathrm{CI}_{1-\alpha}(p) = \left[\hat p \pm \frac{q_\alpha (1 - \bar X_n^{(N)})^{1/N - 1}\sqrt{\bar X_n^{(N)}(1 - \bar X_n^{(N)})}}{\sqrt n\, N}\right],
$$

with $q_\alpha$ the standard normal quantile of order $1 - \alpha/2$.
2. *Precision and optimal pool size.* Almost surely the interval width is asymptotic to

$$
\frac{2q_\alpha}{\sqrt n}\,\frac{1-p}{N}\sqrt{\frac{1 - (1-p)^N}{(1-p)^N}} .
$$

For fixed number of tests $n$, the prefactor is minimized at

$$
N_{\mathrm{opt}} = -\frac{c_\star}{\log(1-p)}, \qquad c_\star = 2 + W(-2e^{-2}) \approx 1.59,
$$

with $W$ the Lambert $W$ function; equivalently $(1-p)^{N_{\mathrm{opt}}} \approx 0.20$, so about 80% of pools test positive at the optimum (unlike Dorfman's design for case identification).
3. *Dilution-induced false negatives.* Model a pool's RT-qPCR cycle threshold as $Y^{(N)} = \min\bigl(\log_2 N - \log_2 \sum_{j=1}^N Z_jC_j,\ c_{\mathrm{cens}}\bigr) + \epsilon$, with $Z_j$ i.i.d. Bernoulli$(p)$ infection indicators, $C_j$ i.i.d. viral loads of infected samples, censoring (positivity) threshold $c_{\mathrm{cens}}$ and Gaussian measurement error $\epsilon$. Neglecting measurement error, a pool containing a single infected sample is detected with probability

$$
\Phi\bigl(c_{\mathrm{cens}}^{(N)}\bigr) = \mathbb{P}\bigl[-\log_2 C \le c_{\mathrm{cens}} - \log_2 N\bigr],
$$

so the false-negative risk $1 - \Phi(c^{(N)}_{\mathrm{cens}})$ grows with $N$. Then $\hat p$ estimates $p\,\Phi(c^{(N)}_{\mathrm{cens}})$, and the corrected interval is

$$
\mathrm{CI}_{1-\alpha}(p) = \left[\frac{\hat p}{\Phi(c^{(N)}_{\mathrm{cens}})} \pm \frac{q_\alpha}{\sqrt n}\,\frac{(1 - \bar X_n^{(N)})^{1/N-1}\sqrt{\bar X_n^{(N)}(1 - \bar X_n^{(N)})}}{N\,\Phi(c^{(N)}_{\mathrm{cens}})}\right].
$$

Numerically (prevalence 3%, viral-load law fitted to clinical data) the optimal pool size with false negatives stays close to $N_{\mathrm{opt}}$ for perfect tests, and pooling cuts the number of tests needed for a given precision about twentyfold, at the price of sampling more individuals.

## Proof sketch

$\bar X_n^{(N)}$ is the empirical mean of a Bernoulli sample with mean $f(p) = 1 - (1-p)^N$, so it is strongly consistent and asymptotically normal for $f(p)$; since $f^{-1}(x) = 1 - (1-x)^{1/N}$ is $C^1$ on $[0,1)$, the delta method and Slutsky's lemma transfer these properties to $\hat p = f^{-1}(\bar X_n^{(N)})$ with asymptotic standard deviation $(f^{-1})'(f(p))\sqrt{f(p)(1-f(p))/n}$, which gives the interval and its width. Minimizing $\frac{1-p}{N}\sqrt{(1-p)^{-N} - 1}$ over $N$ with $x = -N\log(1-p)$ reduces to minimizing $x^{-2}(e^{x} - 1)$, whose stationarity condition $(x - 2)e^x + 2 = 0$ has root $x = 2 + W(-2e^{-2})$. Since viral loads span orders of magnitude, a pool's measured load is essentially the largest individual load diluted by $N$, shifting $C_t$ by $\log_2 N$; this is why pooled $C_t$ values cannot count positives within a pool, and why detection probability is the stated tail probability.

## Sources

- Vincent Brault, Bastien Mallein and Jean-François Rupprecht, "Group testing as a strategy for COVID-19 epidemiological monitoring and community surveillance", *PLOS Computational Biology* 17 (2021), e1008726, <https://doi.org/10.1371/journal.pcbi.1008726>. Preprint version: arXiv:2005.06776 (2020), Section I (prevalence estimator lemma and optimal pool size), Section II (pooled $C_t$ model) and Section IV (false-negative correction), <https://doi.org/10.48550/arXiv.2005.06776>.
