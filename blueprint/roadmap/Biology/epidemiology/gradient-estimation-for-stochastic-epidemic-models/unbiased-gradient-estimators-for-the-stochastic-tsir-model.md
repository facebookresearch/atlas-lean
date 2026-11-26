# Unbiased gradient estimators for outbreak size in the stochastic TSIR model

**Model.** In a population of size $N$ with $i_0$ initial infectives, a random number $V \sim \mathrm{Bin}(N - i_0, v)$ of the others is immunized, so $S_0 = N - i_0 - V$. The discrete-time stochastic SIR (TSIR) chain $\mathbf{X}_t = (S_t, I_t)$ evolves by $I_{t+1} = \min(Y_t, S_t)$ and $S_{t+1} = S_t - I_{t+1}$. Given $S_t = s > 0$ and $I_t = i > 0$, $Y_t$ is negative binomial with mean $\beta s i/N$ and shape $i$:

$$
P_Y(y \mid s, i; \beta) = \frac{\Gamma(i + y)}{y!\, \Gamma(i)} \Big(\frac{i}{i + \beta s i/N}\Big)^{i} \Big(\frac{\beta s i/N}{i + \beta s i/N}\Big)^{y}, \qquad y = 0, 1, 2, \dots
$$

The chain is absorbed once $s = 0$ or $i = 0$. Let $Z(v, \beta, T) = \sum_{t=1}^{T} I_t$ be the outbreak size up to time $T$, and let $J_v = \frac{d}{dv}\mathbb{E}[Z]$ and $J_\beta = \frac{d}{d\beta}\mathbb{E}[Z]$.

**Weak-derivative estimator for $J_v$.** Since $\frac{d}{dv}\mu(\cdot; v) = (N - i_0)(\mu^+ - \mu^-)$, where $\mu^+$ is the law of $1 + \mathrm{Bin}(N - i_0 - 1, v)$ and $\mu^-$ that of $\mathrm{Bin}(N - i_0 - 1, v)$, the estimator

$$
\widehat J_{v,K} = \frac{N - i_0}{K} \sum_{k=1}^{K} (Z_k^+ - Z_k^-)
$$

built from outbreak sizes simulated with initial immunes drawn from $\mu^+$ and $\mu^-$ (possibly coupled) is unbiased: $\mathbb{E}[\widehat J_{v,K}] = J_v$.

**Likelihood-ratio estimator for $J_\beta$.** $J_\beta = \mathbb{E}\big[ Z \sum_{j=0}^{T-1} \partial_\beta \log P(\mathbf{X}_{j+1} \mid \mathbf{X}_j; \beta) \big]$. This equals $\mathbb{E}\big[\sum_{j=0}^{T-1} \big(\sum_{t=j+1}^{T} I_t\big) \partial_\beta \log P(\mathbf{X}_{j+1} \mid \mathbf{X}_j; \beta)\big]$, since future scores have mean zero given the past, and every score is bounded:

$$
\Big| \frac{\partial \log P(\mathbf{X}_{j+1} \mid \mathbf{X}_j; \beta)}{\partial \beta} \Big| \le \frac{N}{\beta}.
$$

**Proposition (parametric uncertainty).** If $\hat v$ has support in $(0,1)$ and $\hat\beta > 0$ satisfies $\mathbb{E}[1/\hat\beta] < \infty$, then both averaged sensitivities $\mathbb{E}_{\hat v, \hat\beta}[J_v]$ and $\mathbb{E}_{\hat v, \hat\beta}[J_\beta]$ are finite, and the estimators stay unbiased after averaging over the uncertain parameter: $\mathbb{E}_{\hat\beta}[\widehat J_v(v, \hat\beta, T)] = J_v(\hat\beta)$ and $\mathbb{E}_{\hat v}[\widehat J_\beta(\hat v, \beta, T)] = J_\beta(\hat v)$, where the right-hand sides are the derivatives of the parameter-averaged expected outbreak size.

## Depends on

- [Stochastic SIR epidemic and its law of large numbers](../../epidemiology/stochastic-sir-epidemic-and-its-law-of-large-num/README.md)

## Expansion

The state space up to time $T$ is finite, so derivatives pass through the sum over paths. Only the initial law depends on $v$, which gives the weak-derivative identity; only the transitions depend on $\beta$, which gives the score-function identity. With $|J_v| \le 2N^2$ and $|J_\beta| \le N T\, \mathbb{E}[N/\beta]$, dominated convergence moves the derivatives through the outer expectation over Bayesian-calibrated parameters. Averaging over parameter uncertainty reduces the estimated indirect (herd-immunity) effect of vaccination, and cost-balancing optimization then chooses more conservative policies.

## Sources

- Nicholas R. Wu, Michael C. Fu, "Sensitivity Analysis and Optimization of Stochastic Epidemic Models under Parameter Uncertainty", arXiv (2026). Sections on the weak-derivative estimator for $J_v$ and the likelihood-ratio estimator for $J_\beta$: unbiasedness proposition, score-bound lemma, summation-rearrangement lemma, parametric-uncertainty proposition. <https://doi.org/10.48550/arXiv.2607.01476>
