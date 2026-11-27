# Sequential Monte Carlo samplers give unbiased normalizing-constant estimates

Let $E_0,\dots,E_T$ be finite sets ($T\ge1$), let $\gamma_t:E_t\to[0,\infty)$ have $Z_t=\sum_x\gamma_t(x)>0$, and put $\pi_t=\gamma_t/Z_t$. Let $K_t$ be Markov kernels from $E_{t-1}$ to $E_t$ (forward kernels) and $L_{t-1}$ Markov kernels from $E_t$ to $E_{t-1}$ (backward kernels), with the absolute-continuity condition

$$\gamma_t(x_t)\,L_{t-1}(x_t,x_{t-1})>0\ \Longrightarrow\ \gamma_{t-1}(x_{t-1})\,K_t(x_{t-1},x_t)>0 .$$

The incremental weight is

$$\tilde w_t(x_{t-1},x_t)=\frac{\gamma_t(x_t)\,L_{t-1}(x_t,x_{t-1})}{\gamma_{t-1}(x_{t-1})\,K_t(x_{t-1},x_t)}$$

where the denominator is positive, and $0$ otherwise. Fix $N\ge1$. Draw $X_0^1,\dots,X_0^N$ iid from $\pi_0$ and set $\hat X_0^i=X_0^i$. For $t=1,\dots,T$: draw $X_t^i\sim K_t(\hat X_{t-1}^i,\cdot)$ independently and set $w_t^i=\tilde w_t(\hat X_{t-1}^i,X_t^i)$; then, if $t<T$, resample multinomially, drawing $\hat X_t^1,\dots,\hat X_t^N$ independently from $\{X_t^j\}$ with probabilities proportional to $w_t^j$ (uniformly if all $w_t^j=0$). The estimator

$$\widehat Z_T=\prod_{t=1}^T\frac1N\sum_{i=1}^Nw_t^i$$

satisfies $\mathbb E\,\widehat Z_T=Z_T/Z_0$ for every $N\ge1$. For $T=1$ this is the unbiasedness of importance sampling of $\gamma_1\otimes L_0$ under $\pi_0\otimes K_1$; the case $N=1$ is included. If instead the initial particles are drawn from a law $\eta_0$ with $\eta_0>0$ where $\gamma_0>0$, the same holds after including the initial weights $\gamma_0(X_0^i)/(Z_0\,\eta_0(X_0^i))$ as a factor $\frac1N\sum_i\gamma_0(X_0^i)/(Z_0\eta_0(X_0^i))$ in $\widehat Z_T$ and resampling the initial particles with these weights.

## Proof depends on

- [Self-normalized importance sampling: ratio consistency, O(1/n) bias, effective sample size](self-normalized-importance-sampling-ratio-consis.md)
- [Change of measure for importance weights](integral-weight-mul.md)

## Expansion

A proof conditions on the particles at time $t-1$: absolute continuity and $\sum_{x_{t-1}}L_{t-1}(x_t,x_{t-1})=1$ give $\sum_{x_{t-1},x_t}\pi_{t-1}(x_{t-1})K_t(x_{t-1},x_t)\tilde w_t(x_{t-1},x_t)=Z_t/Z_{t-1}$, and an induction on $T$ through the multinomial resampling step (the Feynman–Kac martingale argument) gives the product formula. The page should state the induction hypothesis as an identity for $\mathbb E[\widehat Z_t\,\frac1N\sum_i\varphi(X_t^i)\,w_t^i]$ for test functions $\varphi$. Unbiasedness is what makes $\widehat Z_T$ usable in [pseudo-marginal Metropolis–Hastings](pseudo-marginal-mh-exactness-with-unbiased-nonne.md).

## Sources

- P. Del Moral, A. Doucet and A. Jasra, *Sequential Monte Carlo samplers*, J. R. Stat. Soc. B 68 (2006), <https://www.stats.ox.ac.uk/~doucet/delmoral_doucet_jasra_sequentialmontecarlosamplersJRSSB.pdf>, Sec. 3.1–3.2.1, incremental weights (12) and the normalizing-constant estimator (14).
- A. Kong, J. S. Liu and W. H. Wong, *Sequential imputations and Bayesian missing data problems* (1994), sequential importance sampling (background).
