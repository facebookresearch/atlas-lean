# Limit of the direct-method information estimate under non-stationarity

**Setting.** A time-varying stimulus $S_1,\dots,S_n$ is presented on each of $m$ trials. The neural response at time $t$ on trial $k$ is a *word* $R_t^k$: the pattern of spike counts in $L$ adjacent time bins, taking values in a countable set. The **direct method** (plug-in estimate) uses the empirical distributions

$$\hat P_t(r)=\frac1m\sum_{k=1}^m\mathbf 1\{R_t^k=r\},\qquad \hat P(r)=\frac1n\sum_{t=1}^n\hat P_t(r),$$

their entropies $\hat H=-\sum_r\hat P\log\hat P$ (total entropy) and $\hat H_t=-\sum_r\hat P_t\log\hat P_t$ (noise entropy), and the information estimate $\hat I=\hat H-\frac1n\sum_t\hat H_t$.

*Repeated trial assumption:* conditional on the stimulus, the trials $\{S_t,R_t^k\}_t$, $k=1,\dots,m$, are i.i.d. Let $P_t(r)=P(R_t^k=r\mid S_1,\dots,S_n)$ be the conditional response law at time $t$, and $\bar P=\frac1n\sum_tP_t$ its time average.

**Statement.**

1. *(Divergence identity.)* $\hat I=\frac1n\sum_{t=1}^n\hat D(P_t\|\bar P)$, where $\hat D(P_t\|\bar P)=\sum_r\hat P_t(r)\log\frac{\hat P_t(r)}{\hat P(r)}$.
2. *(Limit as trials grow.)* Suppose every $P_t$ has finite entropy. Under the repeated trial assumption, with probability $1$,

$$\lim_{m\to\infty}\hat I=H(\bar P)-\frac1n\sum_{t=1}^nH(P_t)=\frac1n\sum_{t=1}^nD(P_t\|\bar P),$$

and, uniformly in $t$, $\hat H\to H(\bar P)$, $\hat H_t\to H(P_t)$ and $\hat D(P_t\|\bar P)\to D(P_t\|\bar P)$.

So without stationarity the direct-method estimate does not converge to the mutual information between stimulus and response. It converges to the time-averaged Kullback–Leibler divergence between the instantaneous response law and the time-averaged response law. This quantity measures how much the response distribution varies over the course of the stimulus, conditional on that stimulus. It equals a mutual information only after extra assumptions such as stationarity and ergodicity, and its value depends on the particular stimulus realization. Plotting coverage-adjusted estimates of $D(P_t\|\bar P)$ against $t$ shows this time-varying variability directly.

## Expansion

Item 1 is algebra: $\hat H-\hat H_t$ averaged over $t$ equals $\frac1n\sum_t\sum_r\hat P_t\log(\hat P_t/\hat P)$, because $\hat P$ is the average of the $\hat P_t$. For item 2, the strong law of large numbers gives $\hat P_t(r)\to P_t(r)$ a.s. for each $t,r$, and hence $\hat P\to\bar P$. On a countable alphabet, pointwise convergence of probabilities does not by itself give convergence of entropies, since the tail can carry entropy. The proof uses a generalized dominated convergence lemma: if $|f_m|\le g_m$, $f_m\to f$ and $\int g_m\to\int g<\infty$, then $\int f_m\to\int f$. It is applied to the entropy sums over the alphabet, with the finite-entropy assumption controlling the dominating sequence. The divergence form then shows the limit is a time average of KL divergences rather than $I(S;R)$.

These are the divergence proposition and the main theorem of Section 3, with the dominated-convergence lemma of the appendix, of the source.

## Proof depends on

- [Strong law of large numbers from the ergodic theorem](../../../Dynamics/ergodic-theory/birkhoff-ergodic-theorem/tendsto-average-coordinates-ae.md)

## Sources

- V. Q. Vu, B. Yu, R. E. Kass, "Information In The Non-Stationary Case", arXiv:0806.3978 (2008). <https://doi.org/10.48550/arXiv.0806.3978>
