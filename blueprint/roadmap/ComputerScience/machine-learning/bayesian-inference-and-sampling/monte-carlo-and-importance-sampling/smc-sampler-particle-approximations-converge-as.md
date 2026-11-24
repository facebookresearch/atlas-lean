# Particle approximations of sequential Monte Carlo samplers converge

Let $E_0,\dots,E_T$ be measurable spaces, $\gamma_t$ unnormalized target densities with respect to reference measures and normalizing constants $Z_t>0$, $\pi_t=\gamma_t/Z_t$, and run the [sequential Monte Carlo sampler](smc-sampler-unbiasedness-of-the-normalizing-cons.md) with measurable forward kernels $K_t$, backward kernels $L_{t-1}$, initial particles iid from $\pi_0$ and multinomial resampling at every step. Assume the incremental weights are bounded: $0\le\tilde w_t\le C_t<\infty$ for $t=1,\dots,T$. For bounded measurable $f:E_T\to\mathbb R$ let

$$\pi_T^N(f)=\sum_{i=1}^NW_T^i\,f(X_T^i),\qquad W_T^i=\frac{w_T^i}{\sum_jw_T^j},$$

with $\pi_T^N(f)=0$ when all $w_T^j=0$. Then for each fixed $T$ there is a constant $c_T$, depending on $T$, the bounds $C_t$ and the ratios $Z_t/Z_{t-1}$ but not on $N$ or $f$, such that

$$\mathbb E\bigl[(\pi_T^N(f)-\pi_T(f))^2\bigr]\le\frac{c_T\,\|f\|_\infty^2}{N},$$

and in particular $\pi_T^N(f)\to\pi_T(f)$ in probability as $N\to\infty$. For $T=0$, $\pi_0^N(f)=N^{-1}\sum_if(X_0^i)$ and the bound is the variance of an average of $N$ iid draws.

## Depends on

- [Sequential Monte Carlo samplers give unbiased normalizing-constant estimates](smc-sampler-unbiasedness-of-the-normalizing-cons.md)

## Proof depends on

- [Self-normalized importance sampling: ratio consistency, O(1/n) bias, effective sample size](self-normalized-importance-sampling-ratio-consis.md)

## Expansion

A proof inducts on $t$, controlling separately the error of the mutation step (conditionally iid draws given the resampled particles), of the reweighting step (a ratio of two averages whose denominator is bounded below in probability because its mean is $Z_t/Z_{t-1}>0$ and the weights are bounded), and of multinomial resampling (conditionally iid draws from the weighted empirical measure). The page should make $c_T$ explicit and show that the event of zero total weight has probability at most $e^{-\kappa N}$ for some $\kappa>0$. The central limit theorem of the source, with the asymptotic variance in its Proposition 2, is a separate statement.

## Sources

- P. Del Moral, A. Doucet and A. Jasra, *Sequential Monte Carlo samplers*, J. R. Stat. Soc. B 68 (2006), <https://www.stats.ox.ac.uk/~doucet/delmoral_doucet_jasra_sequentialmontecarlosamplersJRSSB.pdf>, Sec. 3.2.1, the particle approximation (13), and Proposition 2 (central limit theorem, under the integrability conditions it cites), convergence of SMC samplers.
