# Cumulated time-rescaling test with subsampled plug-in

**Setting.** A point process $N$ on $[0,T_{\max}]$ with conditional intensity $\lambda(\cdot)$ has compensator $\Lambda(t) = \int_0^t\lambda(u)\,du$. By the time-rescaling theorem, $\{\Lambda(T) : T \in N\}$ is a homogeneous Poisson process of rate $1$ on $[0,\Lambda(T_{\max})]$. Let $K$ denote the Kolmogorov distribution, the law of $\sup_{u\in[0,1]}|B(u)|$ for a Brownian bridge $B$.

**Plug-in lemma.** If $X_1,\dots,X_p$ are i.i.d. with continuous c.d.f. $F$, empirical c.d.f. $F_p$, and $\hat F$ satisfies $\sqrt p\,\sup_x|\hat F(x) - F(x)| \to 0$ in probability, then $\sqrt p\,\sup_x|F_p(x) - \hat F(x)| \to K$ in law. This fails for parametric $\hat F$ fitted on the same data, but holds when $\hat F$ is fitted on a much larger disjoint sample and the test uses a subsample of size $p \ll n$.

**Theorem (cumulated test).** Let $N_1,\dots,N_p$ be i.i.d. processes with conditional intensities $\lambda_i$ and non-negative estimates $\hat\lambda_i$ with

$$p^{-1/2}\sum_{i=1}^p\int_0^{T_{\max}}|\hat\lambda_i(u) - \lambda_i(u)|\,du \xrightarrow{P} 0.$$

Rescale trial $i$ by $\hat\Lambda_i(t) = \int_0^t\hat\lambda_i$ and concatenate the rescaled trials end to end into a process $\hat N^{c,p}$. Then for every $\theta$ with $E\,\Lambda_1(T_{\max}) > \theta$,

$$\sqrt{\hat N^{c,p}([0,p\theta])}\;\sup_{u\in[0,1]}\Big|\frac{1}{\hat N^{c,p}([0,p\theta])}\sum_{X\in\hat N^{c,p},\,X\le p\theta}\mathbf 1\{X/(p\theta) \le u\} - u\Big| \xrightarrow{L} K.$$

Rejecting when the statistic exceeds the $1-\alpha$ quantile of $K$ gives a test of asymptotic level $\alpha$ for the model class used to build $\hat\lambda_i$ (e.g. inhomogeneous Poisson or Hawkes).

## Expansion

Concatenating unit-rate Poisson processes yields a unit-rate Poisson process on $[0,\sum_i\Lambda_i(T_{\max})]$; because this length is random, the test is restricted to the deterministic window $[0,p\theta]$, which it covers with probability tending to one when $E\Lambda_1(T_{\max}) > \theta$. Conditionally on the count, the points in the window are i.i.d. uniform, giving the Kolmogorov limit, and the $p^{-1/2}$ rate condition makes the estimated rescaling an asymptotically negligible perturbation. For Poisson processes one may instead aggregate (superpose) trials: the superposition of $p$ i.i.d. Poisson processes with compensator $\Lambda$ is Poisson with compensator $p\Lambda$, and conditionally on its count its points are i.i.d. with c.d.f. $\Lambda(t)/\Lambda(T_{\max})$. The plug-in lemma explains the classical failure: an estimate fitted on the tested data is correlated with the empirical c.d.f., making the standard critical values wrong.

## Sources

- P. Reynaud-Bouret, V. Rivoirard, F. Grammont, C. Tuleau-Malot, "Goodness-of-fit tests and nonparametric adaptive estimation for spike train analysis", Journal of Mathematical Neuroscience 4 (2014) 3, Sections 1–2, Propositions 1–2, Theorem 1 (Eq (7)) and Tests 2–5, <https://doi.org/10.1186/2190-8567-4-3>, PMCID PMC4021619.
