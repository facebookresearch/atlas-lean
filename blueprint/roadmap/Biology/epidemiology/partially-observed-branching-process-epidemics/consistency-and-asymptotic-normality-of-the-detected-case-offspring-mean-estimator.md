# Consistency and asymptotic normality of the detected-case offspring-mean estimator

In a partially observed branching process, $X_n$ infectious individuals in generation $n$ cannot be observed, and only the number $Z_n$ of detected cases is seen:
$$
X_0=1,\qquad Z_n=\sum_{i=1}^{X_n}\delta_{ni},\qquad X_{n+1}=\sum_{i=1}^{X_n}\big[X_{ni}(1-\delta_{ni})+X'_{ni}\delta_{ni}\big].
$$
Here $\delta_{ni}\sim\mathrm{Bernoulli}(\pi)$, $0<\pi<1$, indicates detection. $X_{ni}$ and $X'_{ni}$ are the offspring numbers of undetected and detected individuals, i.i.d. with finite fourth moments and with the detected offspring law stochastically smaller. All variables are independent. Then $(X_n,Z_n)$ is a Markov chain, and $X_n$ is a Bienaymé–Galton–Watson process with offspring mean $m$, the mean of the $(1-\pi):\pi$ mixture of the two offspring laws. Let $\sigma^2$ be its variance and $m_-$ the mean offspring of a detected individual. With $n_0=\lfloor(n-1)/2\rfloor$, define the estimator built only from detected counts,
$$
\widehat m_{n,o}=\frac{\sum_{k=0}^{n_0}Z_{2k+1}}{\sum_{k=0}^{n_0}Z_{2k}}.
$$

**Theorem.** As $n\to\infty$, on the survival event $\{X_n\to\infty\}$:

1. $\widehat m_{n,o}\to m$ almost surely.
2. $\gamma^{-1}\sqrt{\sum_{k=0}^{n_0}Z_{2k}}\,\big(\widehat m_{n,o}-m\big)$ converges in law to $N(0,1)$, conditionally on $\{X_n\to\infty\}$, where
$$
\gamma^2=(1-\pi)m+\pi\sigma^2+(1+\pi)m^2-2\pi mm_- .
$$

So the epidemic's reproduction number can be estimated consistently from surveillance counts alone, with explicit asymptotic confidence intervals. Two ratio-type estimators based on the full $(X_n,Z_n)$ history are also strongly consistent on survival.

## Depends on

- [Branching-process approximation of early epidemics](../branching-process-approximation-of-early-epidemi/README.md)

## Expansion

Given $X_n$, the count $Z_n$ is $\mathrm{Binomial}(X_n,\pi)$, so $\mathbb E[Z_{n+1}\mid\mathcal F_n]=\pi m X_n$ while $\mathbb E[Z_n\mid X_n]=\pi X_n$. Summing over alternate generations makes numerator and denominator asymptotically proportional with ratio $m$. Using only alternate generations limits the dependence between consecutive terms. A martingale central limit theorem with random norming gives part 2. The extra variance in $\gamma^2$ comes from detection and from the different offspring law of detected individuals.

## Sources

- M. González, I. M. del Puerto and M. Serrano-Pastor, "Particle filtering methods for partially observed branching processes", arXiv:2605.20987 (2026), Section 2 (model (def), consistency theorems for the full-history estimators and Theorem (ta) for $\widehat m_{n,o}$). <https://doi.org/10.48550/arXiv.2605.20987>
